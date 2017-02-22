/************
/DaikonTraceLib.c
/authors: Arijit Chattopadhyay (https://github.com/arijitvt/RTool), Abraham Chan (Integration with LLFI)
/  This library should be linked against programs that have had the LLFI DaikonTrace LLVM
/  pass performed on them
*************/

#include <stdio.h>
#include <stdarg.h>
#include <string.h>
#include <pthread.h>
#include <math.h>

#define TRUE 1
#define FALSE 0

#define SIZE 100
#define BIGSIZE 1000
#define SMALL 30

typedef int bool;

static __thread int callStackCounter  = 0 ;
static const char *fileName = "program.dtrace";
FILE *fp;
static pthread_mutex_t lock = PTHREAD_MUTEX_INITIALIZER;

static __thread int threadId;

//This contains the ower-threadid from inpect;
static int currentLockOwerId = -1; 
static bool isCurrentOwnerOfLock();
//Use this api to lock unlock instead of the 
//pthread_mutex_lock or
//pthread_mutex_unlock
void std_lock();
void std_unlock();

						
static int flagToWriteVersionIntoDtrace = 0;

void writeInfoIntoDtrace() {
	flagToWriteVersionIntoDtrace = 1;
	fp = fopen(fileName,"a");
	const char *data = "input-language C/C++\ndecl-version 2.0\nvar-comparability none\n\n";
	if(fp != NULL) {
		fputs(data,fp);
		fputs("\n",fp);
		fclose(fp);
	}
}

//Must be called after acquiring a lock
void write_thread_nonce(FILE *fp) {
	pthread_t tt = pthread_self();
	int id = (int) tt;
	char buffer[SIZE];

	fputs("this_invocation_nonce",fp);
	fputs("\n",fp);

	memset(buffer,'\0',SIZE);
	sprintf(buffer,"%d",id+callStackCounter);
	fputs(buffer,fp);
	fputs("\n",fp);
}

void clap_hookFuncBegin(int varCount, ...) {
	std_lock();

	if(flagToWriteVersionIntoDtrace == 0) {
		writeInfoIntoDtrace();
	}
	fp = fopen(fileName,"a");
	if(fp != NULL) {

		char buffer[BIGSIZE];
		va_list vararg;
		va_start(vararg,varCount);
		char *funcName = va_arg(vararg,char*);
		
		fputs(funcName,fp);
		fputs("\n",fp);

		write_thread_nonce(fp);

		int i ;
		int j ;

		for( i = 0 ; i < varCount ;++i) {
			char *varName = va_arg(vararg,char*);
			char *varType = va_arg(vararg,char*);
			
			if(strcmp(varType,"int[]") ==0 ) {
				int *data = va_arg(vararg,int*);

				fputs(varName,fp);
				fputs("\n",fp);
				memset(buffer,'\0',BIGSIZE);

				fputs("[",fp);
				for( j = 0 ; j < sizeof(data) ;++j) {
					if (isnan(data[j])) {
						sprintf(buffer," NaN");
					}
					else {
						sprintf(buffer," %d",data[j]);
					}
					fputs(buffer,fp);
				}		
				fputs(" ]",fp);

				fputs("\n",fp);
				fputs("1\n",fp);
				memset(buffer,'\0',BIGSIZE);
			}
			else if(strcmp(varType,"int") ==0 ){
				int data = va_arg(vararg,int);

				fputs(varName,fp);
				fputs("\n",fp);
				memset(buffer,'\0',BIGSIZE);
				sprintf(buffer,"%d",data);
				fputs(buffer,fp);
				fputs("\n",fp);
				fputs("1\n",fp);
			}
			else if(strcmp(varType,"float") ==0 ){
				double data = va_arg(vararg,double);

				fputs(varName,fp);
				fputs("\n",fp);
				memset(buffer,'\0',BIGSIZE);
				sprintf(buffer,"%f",data);
				fputs(buffer,fp);
				fputs("\n",fp);
				fputs("1\n",fp);
			}
			else if(strcmp(varType,"double") ==0 ){
				double data = va_arg(vararg,double);

				fputs(varName,fp);
				fputs("\n",fp);
				memset(buffer,'\0',BIGSIZE);
				sprintf(buffer,"%f",data);
				fputs(buffer,fp);
				fputs("\n",fp);
				fputs("1\n",fp);
			}
			else if(strcmp(varType,"double[]") ==0 ){
				double *data = va_arg(vararg,double*);

				fputs(varName,fp);
				fputs("\n",fp);
				memset(buffer,'\0',BIGSIZE);
			
				fputs("[",fp);
				for( j = 0 ; j < sizeof(data) ;++j) {
					if (isnan(data[j])) {
						sprintf(buffer," NaN");
					}
					else {
						sprintf(buffer," %f",data[j]);
					}
					fputs(buffer,fp);
				}		
				fputs(" ]",fp);
			
				fputs("\n",fp);
				fputs("1\n",fp);
			}
			else if(strcmp(varType,"char") ==0 ){
				int data = va_arg(vararg,int);

				fputs(varName,fp);
				fputs("\n",fp);
				memset(buffer,'\0',BIGSIZE);
				sprintf(buffer,"%d",data);
				fputs(buffer,fp);
				fputs("\n",fp);
				fputs("1\n",fp);
			}
			else if(strcmp(varType,"char*") ==0 ){
				char *data = (char *) va_arg(vararg,int*);

				fputs(varName,fp);
				fputs("\n",fp);
				memset(buffer,'\0',BIGSIZE);
			
				sprintf(buffer,"%s",data);
				fputs(buffer,fp);

				fputs("\n",fp);
				fputs("1\n",fp);
			}

		}
		fputs("\n",fp);
		fclose(fp);
		++callStackCounter;
	}
	std_unlock();
}


void clap_hookFuncEnd(int varCount, ...) {
	std_lock();

	fp = fopen(fileName,"a");
	if(fp != NULL) {
		--callStackCounter;

		char buffer[BIGSIZE];
		va_list vararg;
		va_start(vararg,varCount);
		char *funcName = va_arg(vararg,char*);

		fputs(funcName,fp);
		fputs("\n",fp);

		write_thread_nonce(fp);

		int i ;
		int j ;

		for( i = 0 ; i < varCount ;++i) {
			char *varName = va_arg(vararg,char*);
			char *varType = va_arg(vararg,char*);

			if(strcmp(varType,"int[]") ==0 ) {
				int *data = va_arg(vararg,int*);

				fputs(varName,fp);
				fputs("\n",fp);
				memset(buffer,'\0',BIGSIZE);

				fputs("[",fp);
				for( j = 0 ; j < sizeof(data) ;++j) {
					if (isnan(data[j])) {
						sprintf(buffer," NaN");
					}
					else {
						sprintf(buffer," %d",data[j]);
					}
					fputs(buffer,fp);
				}		
				fputs(" ]",fp);

				fputs("\n",fp);
				fputs("1\n",fp);
				memset(buffer,'\0',BIGSIZE);
			}
			else if(strcmp(varType,"int") ==0 ){
				int data = va_arg(vararg,int);

				fputs(varName,fp);
				fputs("\n",fp);
				memset(buffer,'\0',BIGSIZE);
				sprintf(buffer,"%d",data);
				fputs(buffer,fp);
				fputs("\n",fp);
				fputs("1\n",fp);
			}
			else if(strcmp(varType,"float") ==0 ){
				double data = va_arg(vararg,double);

				fputs(varName,fp);
				fputs("\n",fp);
				memset(buffer,'\0',BIGSIZE);
				sprintf(buffer,"%f",data);
				fputs(buffer,fp);
				fputs("\n",fp);
				fputs("1\n",fp);
			}
			else if(strcmp(varType,"double") ==0 ){
				double data = va_arg(vararg,double);

				fputs(varName,fp);
				fputs("\n",fp);
				memset(buffer,'\0',BIGSIZE);
				sprintf(buffer,"%f",data);
				fputs(buffer,fp);
				fputs("\n",fp);
				fputs("1\n",fp);
			}
			else if(strcmp(varType,"double[]") ==0 ){
				double *data = va_arg(vararg,double*);

				fputs(varName,fp);
				fputs("\n",fp);
				memset(buffer,'\0',BIGSIZE);
			
				fputs("[",fp);
				for( j = 0 ; j < sizeof(data) ;++j) {
					if (isnan(data[j])) {
						sprintf(buffer," NaN");
					}
					else {
						sprintf(buffer," %f",data[j]);
					}
					fputs(buffer,fp);
				}		
				fputs(" ]",fp);
			
				fputs("\n",fp);
				fputs("1\n",fp);
			}
			else if(strcmp(varType,"char") ==0 ){
				int data = va_arg(vararg,int);

				fputs(varName,fp);
				fputs("\n",fp);
				memset(buffer,'\0',BIGSIZE);
				sprintf(buffer,"%d",data);
				fputs(buffer,fp);
				fputs("\n",fp);
				fputs("1\n",fp);
			}
			else if(strcmp(varType,"char*") ==0 ){
				char *data = (char *) va_arg(vararg,int*);

				fputs(varName,fp);
				fputs("\n",fp);
				memset(buffer,'\0',BIGSIZE);
			
				sprintf(buffer,"%s",data);
				fputs(buffer,fp);

				fputs("\n",fp);
				fputs("1\n",fp);
			}
		}
		fputs("\n",fp);
		fclose(fp);
	}
	std_unlock();
}

void hookFaultInjection() {
	std_lock();

	fp = fopen(fileName,"a");

	if(fp != NULL) {
		fputs("FaultInjection",fp);
		fputs("\n",fp);
		fclose(fp);
	}

	std_unlock();
}

void std_lock() {
	pthread_mutex_lock(&lock);
	pthread_t thrd = pthread_self();
	currentLockOwerId = (int) thrd;
}

void std_unlock() {
	currentLockOwerId  = -1;
	pthread_mutex_unlock(&lock);
}

bool isCurrentOwnerOfLock() {
	bool result = FALSE;
	pthread_mutex_t localLock;
	pthread_mutex_init(&localLock,NULL);
	pthread_mutex_lock(&localLock);
	pthread_t thrd = pthread_self();
	int tid = (int) thrd;
	if(tid == currentLockOwerId) {
		result = TRUE;
	}
	pthread_mutex_unlock(&localLock);
	pthread_mutex_destroy(&localLock);
	return result;
}

