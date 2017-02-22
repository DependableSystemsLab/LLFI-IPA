#! /usr/bin/env python3

"""

%(prog)s takes one Daikon invariant file and validates invariants against one or more LLFI Daikon dtrace files

Usage: %(prog)s [OPTIONS] <Daikon Invariants File>
Example1: ValidateInvariants -o DaikonTraceOutput.txt --invariantFile DaikonInvariants.txt --dtraceFile program.dtrace
Example2: ValidateInvariants -o DaikonTraceOutput.txt --invariantFile DaikonInvariants.txt --dtracedir /home/root/dtracefiles/ --outputdir /home/root/outputfiles/

List of options:

-o <output file>:       Output file to hold classified invariants
--dtraceFile:		Single Dtrace file
--dtracedir:		File directory containing DTrace files
--outputdir:		File directory containing Output files
--help(-h):             Show help information
"""

import sys, os
import glob
from collections import OrderedDict, defaultdict
from enum import Enum

prog = os.path.basename(sys.argv[0])


#Global variables
options = {
	"o": "DaikonTraceOutput.txt",
	"invariantFile": "",
	"dtraceFile": "",
	"dtracedir": "",
	"outputdir": "",
	"goldenFile": "",
}

InvariantStrings = (
	("has only one value", "uniqueness"),
	("!= null", "not-null"),
	("sorted by", "order"),
	("one of", "multi-value"),
	("== orig", "initialization"),
	("== [", "array-equality"),
	("elements ==", "element-initialization"),
	("elementwise", "elementwise"),
	("elements", "elementwise"),
	("orig", "initialization"),
	("return", "return-value"),
	(">", "minimum-condition"),
	("<", "maximum-condition"),
	("==", "equality-condition"),
	("!=", "inequality-condition"),
)

OutputHeader = '"LineNumber","FunctionKey","Invariant","Class","TraceID"'

#Enumeration for Error Modes
class ErrorMode(Enum):
	Undefined = -1
	Benign = 0
	SDC = 1
	Crash = 2

FunctionInvariants = {}
VariableValues = {}
DaikonTraceFiles = []
goldenOutput = ""

#Parse command line options
def parseArgs(args):
	global options
	argid = 0
	while argid < len(args):
		arg = args[argid]
		if arg.startswith("-"):
			if arg == "-o":
				argid += 1
				options["o"] = args[argid]
			elif arg == "--help" or arg == "-h": 
				usage()
			elif arg == "--invariantFile": 
				argid += 1
				options["invariantFile"] = args[argid]
			elif arg == "--dtraceFile": 
				argid += 1
				options["dtraceFile"] = args[argid]
			elif arg == "--dtracedir":
				argid += 1
				options["dtracedir"] = args[argid]
			elif arg == "--outputdir":
				argid += 1
				options["outputdir"] = args[argid]
			elif arg == "--goldenFile": 
				argid += 1
				options["goldenFile"] = args[argid]
			else:
				usage("Invalid argument: " + arg)
		argid += 1
	# End of while loop

#Display usage information
def usage(msg = None):
	retval = 0
	if msg is not None:
		retval = 1
		msg = "ERROR: " + msg
		print(msg, file=sys.stderr)
	print(__doc__ % globals(), file=sys.stderr)
	sys.exit(retval)

#Classify the invariant predicate
def parseInvariant(invariant):
	invariant = invariant.lstrip('::')
	invarType = "other"

	orderedInvariantStrings = OrderedDict(InvariantStrings)

	for invarString in orderedInvariantStrings:
		if invarString in invariant: 
			invarType = orderedInvariantStrings[invarString]
			break          
	return (invariant, invarType)

#Helper methods
def getLineCount(fileName):
	return sum(1 for line in open(fileName))

def isSorted(values, order):
	if order == "<":
		return all(values[i] <= values[i+1] for i in range(len(values)-1))
	else:
		return all(values[i] >= values[i+1] for i in range(len(values)-1))

def stringToArray(stringValues):
	return [float(i) for i in stringValues]

def readOrigValue(invocation, funcKey, variableName):
	functionName = funcKey.split(".")[0]
	return VariableValues[(invocation, functionName, variableName)]

def saveOrigValues(invocation, funcKey, variableDict):
	if "ENTER" in funcKey:
		functionName = funcKey.strip(".ENTER")
		for variableName, value in variableDict.items():
			VariableValues[(invocation, functionName, variableName)] = value[0]

def convertValue(stringVal):
	try:
		return int(stringVal)
	except ValueError:
		#try:
		return float(stringVal)
		#except ValueError:
		#	return stringVal

def convertListValueDTrace(stringVal):
	stringValList = stringVal.strip("[] ").split(" ")
	return [convertValue(elem) for elem in stringValList]

def convertListValueDaikon(stringVal):
	stringValList = stringVal.strip("[]").split(", ")
	return [convertValue(elem) for elem in stringValList]

def writeViolatedInvariantToFile(lineNo, funcKey, invariantPredicate, invariantType, latency, errorMode):
	with open(options["o"],"a") as outputFile:
		if errorMode == ErrorMode.Undefined:
	 		outputFile.write('"' + '","'.join([lineNo, funcKey, invariantPredicate, invariantType, str(latency)]) + '"\n')
		else:
	 		outputFile.write('"' + '","'.join([lineNo, funcKey, invariantPredicate, invariantType, str(latency), str(errorMode)]) + '"\n')

def evaluateCompareOp(condition, value, invariantVal):
	invariantHolds = True

	if condition == ">=":
		invariantHolds = (value >= invariantVal)
	elif condition == ">":
		invariantHolds = (value > invariantVal)
	elif condition == "<=":
		invariantHolds = (value <= invariantVal)
	elif condition == "<":
		invariantHolds = (value < invariantVal)
	elif condition == "==":
		invariantHolds = (value == invariantVal)
	elif condition == "!=":
		invariantHolds = (value != invariantVal)

	return invariantHolds

def compareLists(listA, listB):
	equality = True
	if len(listA) != len(listB):
		equality = False	
	else:
		for i in range(len(listA)):
			if listA[i] != listB[i]:
				equality = False
				break
	return equality


def getTraceID(dtraceFileName):
	return dtraceFileName.split(".")[-2]

def checkFailureMode(dtraceFileName):
	global goldenOutput

	runID = getTraceID(dtraceFileName)
	outputDir = options["outputdir"]
	std_outputfile = [outputDir + "std_outputfile", "run", runID]
	stdOutputfileName = "-".join(std_outputfile)
	
	errorMode = ErrorMode.Benign
	
	try:
		if (os.stat(stdOutputfileName).st_size == 0) or (open(stdOutputfileName,"r").read() == "PARSEC Benchmark Suite\n"):
			return ErrorMode.Crash
	except:
		return ErrorMode.Crash

	if not goldenOutput:
		try:
			with open(stdOutputfileName,"r") as o:
				for line in o:
					if "not" in line:
						errorMode = ErrorMode.SDC
			#with open(options["goldenFile"],"r") as o:
			#	goldenOutput = o.read()
		except IOError:
			print("Unable to open ", stdOutputfileName)

	if goldenOutput not in open(stdOutputfileName,"r").read():
		errorMode = ErrorMode.SDC

	return errorMode


#If an invariant is found to be violated, it is printed to output along with the conflicting line number.
#Returns False if invariant is violated. True otherwise.
def evaluateInvariants(invocation, funcKey, valueDict, traceID, errorMode):

	try:
		funcInvariantsList = FunctionInvariants[funcKey]
	except:
		return

	
	for invariant in funcInvariantsList:

		#("Invariant Predicate", "Invariant Type")
		invariantPredicate = invariant[0]
		invariantType = invariant[1]

		invariantVariable = invariantPredicate.split(" ")[0]

		try:
			value = convertValue(valueDict[invariantVariable][0])
		except:
			pass

		invariantHolds = True

		if invariantType == "uniqueness":
			#if type(value) is list:
			#	invariantHolds = False
			pass
	
		elif invariantType == "not-null":
			if value is None:
				invariantHolds = False

		elif invariantType == "order":
			order = invariantPredicate.rsplit(" ")[-1]
			invariantHolds = isSorted(value, order)

		elif invariantType == "multi-value":
			strInvariantVal = invariantPredicate.split("{")[-1].strip("} ")

			if "[" not in strInvariantVal:
				invariantVal = convertListValueDaikon(strInvariantVal)
				invariantHolds = (value in invariantVal)
			else:
				invariantValList = strInvariantVal.split("], ")
				invariantVal = [convertListValueDaikon(elem) for elem in invariantValList]

				value = convertListValueDTrace(valueDict[invariantVariable][0])
				invariantHolds = (value in invariantVal)

		elif invariantType == "array-equality":
			value = convertListValueDTrace(valueDict[invariantVariable][0])

			strInvariantVal = invariantPredicate.split("== [")[1]
			invariantVal = convertListValueDaikon(strInvariantVal)

			invariantHolds = compareLists(invariantVal, value)

		elif invariantType == "elementwise" or invariantType == "element-initialization":
			value = convertListValueDTrace(valueDict[invariantVariable][0])

			strInvariantVal = invariantPredicate.rsplit(" ")[3]

			
			try:
				invariantVal = convertValue(strInvariantVal)
			except:
				if "orig" in strInvariantVal:
					strInvariantVal = strInvariantVal.split("orig(")[1].strip(")")
					invariantVal = convertValue(readOrigValue(invocation, funcKey, strInvariantVal))
				elif "elementwise" in strInvariantVal:
					strInvariantValTemp = invariantPredicate.split(" ")[-2].strip()
					invariantVal = valueDict[strInvariantValTemp][0]
					#invariantVal = convertValue(readOrigValue(invocation, funcKey, strInvariantValTemp))
				else:
					invariantVal = convertValue(valueDict[strInvariantVal][0])

		
			condition = invariantPredicate.rsplit(" ")[-2].strip()

			if "elementwise" not in strInvariantVal:
				for i in range(len(value)):
					if not evaluateCompareOp(condition, value[i], invariantVal):
						invariantHolds = False
						break
			else:
				for i in range(len(value)):
					if not evaluateCompareOp(condition, value[i], invariantVal[i]):
						invariantHolds = False
						break

		elif invariantType != "other":
			strInvariantVal = invariantPredicate.rsplit(" ")[2]
			
			try:
				invariantVal = convertValue(strInvariantVal)
			except:
				if "orig" in strInvariantVal:
					strInvariantVal = strInvariantVal.split("orig(")[1].strip(")")
					try:
						invariantVal = convertValue(readOrigValue(invocation, funcKey, strInvariantVal))
					except:
						invariantHolds = True
				else:
					invariantVal = convertValue(valueDict[strInvariantVal][0])


			condition = invariantPredicate.rsplit(" ")[-2].strip()

			invariantHolds = evaluateCompareOp(condition, value, invariantVal)
	
		if not invariantHolds:
			writeViolatedInvariantToFile(valueDict[invariantVariable][1], funcKey, invariantPredicate, invariantType, traceID, errorMode)
				

def readDaikonInvariantFile():
	global FunctionInvariants
	beginFile = False
	funcKey = ""
	funcInvariantsList = {}
	
	invariantFileName = options["invariantFile"]

	try:
		invariantFile =  open(invariantFileName, 'r')
	except IOError:
		print("Unable to open ",invariantFileName)
		sys.exit(1) 

	for line in invariantFile: # Inner loop:
		line = line.strip('\n')
		if line.startswith("=="):
			beginFile = True
		elif line.startswith("Exiting"):
			break
		elif beginFile: 
			if line.startswith(".."):
				line = line.lstrip("..")
				words = line.split('(')
				funcName = words[0].split(':::')[0]
				entryOrExit = line.rsplit(':::')[-1]
				funcKey = funcName + "." + entryOrExit
				funcInvariantsList[funcKey] = []

			elif not line.startswith("==") and not line.startswith(".."):
				invariant = parseInvariant(line)
				funcInvariantsList[funcKey].append(invariant)

		else:
			pass   # Unimportant line
	# End of inner loop		
	
	invariantFile.close

	FunctionInvariants = {funcKey:invariantList for funcKey, invariantList in funcInvariantsList.items() if invariantList}


def readDTraceFile(dtraceFileName, errorMode=ErrorMode.Undefined):

	try:
		lineCount = getLineCount(dtraceFileName)
		dtraceFile = open(dtraceFileName, 'r')
	except IOError:
		print("Unable to open ",dtraceFileName)
		sys.exit(1) 

	nextLineisInvocation = False
	nextLineisVal = False
	variableDict = {}
	lineNumber = 1
	traceID = getTraceID(dtraceFileName)

	beginReading = 0;

	for line in dtraceFile:

		line = line.strip('\n')
		
		if beginReading == 0:
			if line.startswith(".."):
				beginReading += 1

		if beginReading >= 1:
			
			if line.startswith(".."):
				line = line.lstrip("..")
				functionName = line.split("(")[0]
				functionName = functionName.split(":::")[0]

				entryOrExit = line.rsplit(':::')[-1]
				entryOrExit = "EXIT" if entryOrExit == "EXIT0" else entryOrExit
				funcKey = functionName + "." + entryOrExit

				#Flush variableDict
				variableDict.clear()
			elif line == "this_invocation_nonce":
				nextLineisInvocation = True
			elif nextLineisInvocation:
				invocation = line
				nextLineisInvocation = False
			elif nextLineisVal:
				variableDict[variableName] = (line, str(lineNumber))
				nextLineisVal = False
			elif line == "1":
				pass
			elif line and not line.startswith(".."):
				variableName = line
				nextLineisVal = True
			elif not line:
				#Evaluate a dict of values with a dict of invariants
				saveOrigValues(invocation, funcKey, variableDict)
				evaluateInvariants(invocation, funcKey, variableDict, traceID, errorMode)
			else:
				pass   # Unimportant line
		
		lineNumber += 1
		
	dtraceFile.close
		

def main(args):
	global OutputHeader

	parseArgs(args)

	if options["outputdir"]:
		OutputHeader += ',"FailureMode"'

	outputFileName = options["o"]
	try:
		outputFile = open(outputFileName,"w")
		outputFile.write(OutputHeader + "\n")
	except IOError:
		print("Unable to open ", outputFileName)
		stdout = outputFile
	outputFile.close()

	readDaikonInvariantFile()

	if options["dtracedir"]:
		DaikonTraceFiles.extend(glob.glob(options["dtracedir"] + "*.dtrace"))
		
		for dtraceFile in DaikonTraceFiles:
			if options["outputdir"]:
				errorMode = checkFailureMode(dtraceFile)
			else:
				errorMode = ErrorMode.Undefined

			readDTraceFile(dtraceFile, errorMode)

	else:
		readDTraceFile(options["dtraceFile"])
	
		

if __name__=="__main__":
  main(sys.argv[1:])
