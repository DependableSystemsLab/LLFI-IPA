/***************
DaikonTracePass.cpp
Authors: Arijit Chattopadhyay (https://github.com/arijitvt/RTool), Abraham Chan (Integration with LLFI)
  This llvm pass acts as the front end instrumenter of the Daikon tool
  
  Run the pass with the opt -daikontracepass option after loading LLFI.so
  
  This pass injects a function call at the entry and exit points of 
  every function that prints variable type and value 
  to a file specified during the pass.
***************/

#include "DaikonTracePass.h"
#include "Utils.h"


namespace llfi {

bool DaikonTrace::runOnFunction(Function &F) {

	if (!isInit) {
		
		Module *module = F.getParent();	
		doInit(module);

		generateProgramPoints(module);
		loadProgramPoints(module);
	}

	//Generate function and variable declaration entries
	dumpDeclFileAtEntryAndExit(&F,"ENTRY");
	dumpDeclFileAtEntryAndExit(&F,"EXIT");
	
	//Instrument every function at entry and exit points 
	hookAtFunctionStart(&F);
	hookAtFunctionEnd(&F);

	return true;

}


/**
 * This Function will hook at the beginning of every Function
 */
void DaikonTrace::hookAtFunctionStart(Function *func) {

	if(doNotInstrument(func->getName())) return;

	Module *module = func->getParent();

	vector<Value*> Arguments;
	/**
	 * We will Handle only Integer/Float/Double/Array types and ignore all others for time begin
	 */
	for(Function::arg_iterator argItr = func->arg_begin(); argItr != func->arg_end(); ++argItr) {
		Argument *arg = &*argItr;
		Value *val = static_cast<Value*>(arg);
		StringRef retType(getTypeString(val));
		if (isSupportedType(retType)) {
		 	Arguments.push_back(val);
		}
	}

	int totalArgumentSize = Arguments.size();	
	
	/**
	 * So far the format is varcount,function name, function params
	 * The var count will count function params but not the function name
	 */

	Function *hookFunctionBegin = cast<Function>(module->getOrInsertFunction("clap_hookFuncBegin",functionType));
	vector<Value*> argList;
	Constant *argCount = ConstantInt::get(module->getContext(),APInt(32,totalArgumentSize,true));
	argList.push_back(argCount);

	//Send the function name
	string funcNameStr = func->getName().str();
	string finalNameToSend=".."+getDemangledFunctionName(funcNameStr.c_str())+":::ENTER";
	StringRef finalNameToSendRef (finalNameToSend.c_str());
	Value *funcNameValue = getValueForString(finalNameToSendRef,module);
	argList.push_back(funcNameValue);
	
	/**
	 * The format is  varname -vartype-varvalue
	 */
	//Now Send the parameters
	for(vector<Value*>::iterator ArgItr = Arguments.begin(); ArgItr != Arguments.end(); ++ArgItr) {
		Value *val= *ArgItr;
		Value *valName = getValueForString(val->getName(),module);
		string typeStr = getTypeString(val);
		Value *type=getValueForString(StringRef(typeStr.c_str()).trim(),module);
		argList.push_back(valName);
		argList.push_back(type);
		argList.push_back(val);
	}

	Instruction *target = NULL;

	//To disable this instrumentation and follow the old approach then the comment out
	//the function call to insertDummyStoreIntoFunction
	Instruction *hookFunctionBeginInstruction = CallInst::Create(hookFunctionBegin,argList);

	for(inst_iterator institr = inst_begin(func); institr!= inst_end(func); ++institr) {
		Instruction *ii = &*institr;
		if(!isa<AllocaInst>(ii)) {
			target = ii;
			break;
		}
	}
	hookFunctionBeginInstruction->insertBefore(target);

}


void DaikonTrace::hookAtFunctionEnd(Function *func) {

	if(doNotInstrument(func->getName())) return;

	Module *module = func->getParent();

	vector<Value*> Arguments;
	/**
	 * We will Handle only Integer types and ignore all others for time begin
	 */
	for(Function::arg_iterator argItr = func->arg_begin(); argItr != func->arg_end(); ++argItr) {
		Argument *arg = &*argItr;
		Value *val = static_cast<Value*>(arg);
		StringRef retType(getTypeString(val)) ;
		if(isSupportedType(retType)) {
		 	Arguments.push_back(val);
		}
	}

	int totalArgumentSize = Arguments.size();
	

	/**
	 * So far the format is varcount,function name, function params
	 * The var count will count function params but not the function name
	 */
 
	//First Check the return type
	bool hasReturn = false;
	StringRef returnTypeRef( getTypeString(func->getReturnType()));
	if(isSupportedType(returnTypeRef)) {
		hasReturn = true;
	}

	//Now standard process
	Function *hookFunctionEnd = cast<Function>(module->getOrInsertFunction("clap_hookFuncEnd",functionType));
	vector<Value*> argList;
	Constant *argCount ; 
	if(hasReturn) {
		//One extra for return type
		argCount = ConstantInt::get(module->getContext(),APInt(32,totalArgumentSize+1,true));
	}else {
		argCount = ConstantInt::get(module->getContext(),APInt(32,totalArgumentSize,true));
	}

	argList.push_back(argCount);


	//Send the function name
	string funcNameStr = func->getName().str();
	string finalNameToSend=".."+getDemangledFunctionName(funcNameStr.c_str())+":::EXIT0";
	StringRef finalNameToSendRef (finalNameToSend.c_str());
	Value *funcNameValue = getValueForString(finalNameToSendRef,module);
	argList.push_back(funcNameValue);
	
	/**
	 * The format is  varname -vartype-varvalue
	 */
	//Now Send the parameters
	//for(Function::arg_iterator argItr = func->arg_begin(); argItr != func->arg_end(); ++argItr) {
	for(vector<Value*>::iterator ArgItr = Arguments.begin(); ArgItr != Arguments.end(); ++ArgItr) {
		Value *val= *ArgItr;
		Value *valName = getValueForString(val->getName(),module);
		string typeStr = getTypeString(val);
		Value *type=getValueForString(StringRef(typeStr.c_str()).trim(),module);
		argList.push_back(valName);
		argList.push_back(type);
		argList.push_back(val);
	}

	//First find the return instruction and push the return value if the return is int type
	Instruction *target = NULL;
	for(Function::iterator bbItr = func->begin(); bbItr != func->end(); ++bbItr) {
		Instruction *ii = bbItr->getTerminator();
		if(isa<ReturnInst>(ii)) {
			target= ii;
			break;
		}
	}

	if(hasReturn) {
		ReturnInst *retInst = static_cast<ReturnInst*>(target);
		Value *val= retInst->getReturnValue();
		Value *valName = getValueForString("return",module);
		Value *type=getValueForString(StringRef(getTypeString(val).c_str()).trim(),module);
		argList.push_back(valName);
		argList.push_back(type);
		argList.push_back(val);
	}

	Instruction *hookFunctionEndInstruction = CallInst::Create(hookFunctionEnd,argList);
	hookFunctionEndInstruction->insertBefore(target);


}

/**
 * This Function will create declfile
 * */

void DaikonTrace::dumpDeclFileAtEntryAndExit(Function *func, string EntryOrExit) {
	int tabCount  = 0 ;
	static bool flagToWriteVersionIntoDtrace = true;
	static bool flagToWriteFunctionIntoDtrace = true;
	static string declFileName = "program.dtrace"; 
	string versionInfo = "";

	if (!flagToWriteFunctionIntoDtrace) {
		return;
	}

	if (flagToWriteVersionIntoDtrace) {
		fstream declFileHeader(declFileName,ios::in);

		if (isFileEmpty(declFileHeader)) {
			versionInfo = "input-language C/C++\ndecl-version 2.0\nvar-comparability none\n\n";
			flagToWriteVersionIntoDtrace = false;
			declFileHeader.close();
		}
		else {
			flagToWriteFunctionIntoDtrace = false;
			declFileHeader.close();
			return;
		}
	}
	
	fstream declFile(declFileName,ios::out|ios::app);
	
	if(declFile.is_open()) {
		string functionName = getDemangledFunctionName(func->getName().str().c_str());
		StringRef funcName (functionName.c_str());
		
		if(find(programPoints.begin(),programPoints.end(),funcName) != programPoints.end()) {
			declFile<<versionInfo;
			declFile<<"ppt .."<<funcName.str();
			
			if(EntryOrExit == "ENTRY") {
				declFile<<":::ENTER\n";
				tabCount = 1;
				putTabInFile(declFile,tabCount);
				declFile<<"ppt-type enter\n";
			}else if( EntryOrExit == "EXIT") {

				declFile<<":::EXIT0\n";
				tabCount = 1;
				putTabInFile(declFile,tabCount);
				declFile<<"ppt-type subexit\n";
			}
			
			//Process function Params
			for(Function::arg_iterator argItr = func->arg_begin(); argItr != func->arg_end(); ++argItr) {
				Argument *arg = &*argItr;
				Value *v = static_cast<Value*>(arg);
				string varName = v->getName().trim().str();
				string typeString = getTypeString(v);
				StringRef typeStringRef(typeString);

			    if (!isSupportedType(typeStringRef)) {
					continue;
				}

				tabCount = 1;
				putTabInFile(declFile,tabCount);
				declFile<<"variable "<<varName<<"\n";
				tabCount = 2;
				putTabInFile(declFile,tabCount);
				declFile<<"var-kind variable\n";
				putTabInFile(declFile,tabCount);
				declFile<<"rep-type "<<getTypeString(v)<<"\n";
				putTabInFile(declFile,tabCount);
				declFile<<"dec-type "<<getTypeString(v)<<"\n";
				putTabInFile(declFile,tabCount);
				declFile<<"flags is_param\n";
			}

			if(EntryOrExit == "EXIT") {
			    string returnType = getTypeString(func->getReturnType());
			    if (isSupportedType(returnType)){
				tabCount = 1;
				putTabInFile(declFile,tabCount);
				declFile<<"variable return\n";
				tabCount = 2;
				putTabInFile(declFile,tabCount);
				declFile<<"var-kind variable\n";
				putTabInFile(declFile,tabCount);
				declFile<<"rep-type "<<returnType<<"\n";
				putTabInFile(declFile,tabCount);
				declFile<<"dec-type "<<returnType<<"\n";
			    }
			}

		}
		declFile<<"\n";
		declFile.close();
	}
}

void DaikonTrace::generateProgramPoints(Module *module) {
	fstream pptFile("ProgramPoints.ppts",ios::out);
	if(pptFile.is_open()) { 		
		string modName = module->getModuleIdentifier();
		pptFile<<"Module_Name : " <<modName<<"\n";
		for(Module::iterator funcItr = module->begin(); funcItr != module->end(); ++funcItr) {
			string functionName (getDemangledFunctionName(funcItr->getName().str().c_str()));
			if(doNotInstrument(funcItr->getName())) {
				continue;
			}
			Function *func= &*funcItr;
			if(func->size() == 0 ) {
				continue;
			}
			functionName += " \n";
			pptFile<<functionName;
		}
		pptFile<<"\n";
		pptFile.close();
	}
}


void DaikonTrace::loadProgramPoints(Module *module) {

	ifstream pptFile("ProgramPoints.ppts",ios::in);
	if(pptFile.is_open()){
		string line;

		while(getline(pptFile,line)){			
			StringRef lineRef(line.c_str());
			lineRef = lineRef.trim();		
			//Load only the program points that are related to this module
			if(lineRef.startswith("Module_Name")) {
				continue;
			}
            if( lineRef.size() != 0) {
				programPoints.push_back(lineRef.str());
			}
		}
		
		pptFile.close();
	}
}


//Helper methods

void DaikonTrace::doInit(Module *module) {
	
	voidType = Type::getVoidTy(module->getContext());
	int8Type  = IntegerType::get(module->getContext(),8);
	int32Type = IntegerType::get(module->getContext(),32);
	int64Type = IntegerType::get(module->getContext(),64);
	ptr8Type  = PointerType::get(int8Type,0);
	ptr32Type = PointerType::get(int32Type,0);
	ptr64Type = PointerType::get(int64Type,0);

	ptrPtr32Type = PointerType::get(ptr32Type,0);
	ptrPtr64Type = PointerType::get(ptr64Type,0);

	ptrFloatType = Type::getFloatPtrTy(module->getContext());
	ptrDoubleType = Type::getDoublePtrTy(module->getContext());
	ptrPtrFloatType = PointerType::get(ptrFloatType,0);
	ptrPtrDoubleType = PointerType::get(ptrDoubleType,0);

	structType = StructType::get(module->getContext());
	ptrStructType = PointerType::get(structType,0);
	ptrPtrStructType = PointerType::get(ptrStructType,0);

	functionType = FunctionType::get(voidType,true);
	isInit = true;
}

bool DaikonTrace::DaikonTrace::isGlobal(Value *value) {
	for(vector<Value*>::iterator itr = globalList.begin(); itr != globalList.end() ; ++itr) {
		Value *v = *itr;
		if(value == v) { 
			return true;
		}
	}
	return false;
}

bool DaikonTrace::isSupportedType(StringRef typeName){
	if (typeName.equals("int") || typeName.equals("double") || typeName.equals("float") ||
		typeName.equals("int[]") || typeName.equals("double[]")) {
		return true;
	}
	return false;
}

bool DaikonTrace::doNotInstrument(StringRef funcName) {
	if(funcName.startswith("injectFault") || funcName.find("parsec") != StringRef::npos || funcName.find("Not") != StringRef::npos
	|| funcName.find("sha") != StringRef::npos) {
		return true;
	}
	return false;
}

void DaikonTrace::putTabInFile(fstream &stream, int tabCount) {
	if(stream.is_open()) {
		for(int i = 0 ; i  < tabCount; ++i) {
			stream<<" ";
		}
	}
}

bool DaikonTrace::isFileEmpty(fstream &inputFile) {
	return ( inputFile.peek() == istream::traits_type::eof() );
}

Value* DaikonTrace::getValueForString(StringRef variableName, Module *module) {
	Constant *valueName = ConstantDataArray::getString(module->getContext(), variableName,true);
	Value *val = new GlobalVariable(*module,valueName->getType(), true, GlobalValue::InternalLinkage,valueName);
	return val;
}

string DaikonTrace::find_and_replace(string source, const char find, const string replace) {
	for(string::size_type i = 0; (i = source.find(find, i)) != string::npos;)
	{
		source.replace(i, 1, replace);
		i += replace.length();
	}
	return source;
}

string DaikonTrace::demangle(const char* name) {
        int status = -1; 

        unique_ptr<char, void(*)(void*)> res { abi::__cxa_demangle(name, NULL, NULL, &status), free };
        return (status == 0) ? res.get() : string(name);
}

string DaikonTrace::getDemangledFunctionName(const char* name) {
	string funcName = demangle(name);
	if (funcName == "main") {
		funcName = funcName.append("()");
	}
	return find_and_replace(string(funcName), ' ', "\\_");
}


string DaikonTrace::getTypeString(Value *value) {
        return getTypeString(value->getType());
}


string DaikonTrace::getTypeString(Type *type) {
	switch(type->getTypeID()) {
		case Type::IntegerTyID:{
					       IntegerType *intType=static_cast<IntegerType*>(type);
					       if(intType->getBitWidth() == 8) {
						       return "char";
					       }else if(intType->getBitWidth() == 32|| 
							       intType->getBitWidth() == 64){
						       return "int";
					       }else {
						       return "int";
					       }
				       }

		case Type::FloatTyID:{
					     return "float";
				     }

		case Type::DoubleTyID:  {
						return "double";
					}

		case Type::PointerTyID:{
					 	PointerType *ptrType = static_cast<PointerType*>(type);
					       	if(ptrType  ==  ptr32Type || ptrType == ptr64Type) {
					               	return "int[]";
					       	}else if(ptrType == ptr8Type) {
					       		return "char*";
					       	}else if(ptrType == ptrPtr32Type || ptrType == ptrPtr64Type) {
					       		return "int**";
						}else if(ptrType == ptrFloatType) {
					       		return "float*";
						}else if(ptrType == ptrDoubleType) {
					       		return "double[]";
						}else if(ptrType == ptrPtrFloatType) {
					       		return "float**";
						}else if(ptrType == ptrPtrDoubleType) {
					       		return "double**";
						}else if(ptrType == ptrStructType) {
					       		return "struct*";
						}else if(ptrType == ptrPtrStructType) {
					       		return "struct**";
					       	}else {
					               	return "pointer";
					       	}
				       }
		case Type::ArrayTyID:  {
						return "array";
					}
		case Type::StructTyID:  {
						return "struct";
					}
		case Type::VectorTyID:  {
						return "vector";
					}
		default:  {
					errs()<<"Unable to identify type : "<<type->getTypeID()<<"\n";
			}

	}
	return "unknown";
}

//Register the pass with llvm
static RegisterPass<DaikonTrace> X("daikontracepass", 
    "Instrument function entry and exit points to trace variable values at runtime", 
    false, false);

}//namespace llfi

