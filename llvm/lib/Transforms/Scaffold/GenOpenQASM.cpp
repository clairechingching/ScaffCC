//===- GenOpenQASM.cpp - Generate OpenQASM output -----------===//
//
//                     The LLVM Scaffold Compiler Infrastructure
//
// This file was created by Scaffold Compiler Working Group
//
//===----------------------------------------------------------------------===//

#include <sstream>
#include <algorithm>
#include <string>
#include "llvm/Argument.h"
#include "llvm/Pass.h"
#include "llvm/Module.h"
#include "llvm/Function.h"
#include "llvm/BasicBlock.h"
#include "llvm/Instruction.h"
#include "llvm/Instructions.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/ADT/ilist.h"
#include "llvm/Constants.h"
#include "llvm/Analysis/DebugInfo.h"
#include "llvm/IntrinsicInst.h"

using namespace llvm;
using namespace std;

#define MAX_BT_COUNT 15 //max backtrace allowed - to avoid infinite recursive loops
#define MAX_QBIT_ARR_DIM 5 //max dimensions allowed for qbit arrays

//Set true for debug mode
bool debugGenOpenQASM = false;

namespace{
	enum instType{
		alloca,
		getelementptr,
		load,
		call,
		store,
		br
	};

	struct qGateArg{ //arguments to qgate calls
		Value* argPtr;
		int argNum;
		bool isQbit;
		bool isAbit;
		bool isCbit;
		bool isParam;
		bool isUndef;
		bool isPtr;
		bool isDouble;
		int numDim; //number of dimensions of qbit array
		int dimSize[MAX_QBIT_ARR_DIM]; //sizes of dimensions of array for qbit declarations OR indices of specific qbit for gate arguments
		int valOrIndex; //Value if not Qbit, Index if Qbit & not a Ptr
		double val;
		//Note: valOrIndex is of type integer. Assumes that quantities will be int in the program.
		qGateArg(): argPtr(NULL), argNum(-1), isQbit(false), isAbit(false), isCbit(false), isParam(false), isUndef(false), isPtr(false), isDouble(false), numDim(0), valOrIndex(-1), val(0.0){ }
	};
  
	struct FnCall{ //datapath sequence
		Function* func;
		Value* instPtr;
		std::vector<qGateArg> qArgs;
	};    

	struct GenQASM : public ModulePass {
		static char ID;  //Pass identification, replacement for typeid
		std::vector<Value*> vectQbit;

		std::vector<qGateArg> tmpDepQbit;
		std::vector<qGateArg> allDepQbit;

		map<Function*, vector<qGateArg> > mapQbitsInit;
		map<Function*, vector<qGateArg> > mapFuncArgs;
		map<BasicBlock *, vector<FnCall>> fnCallTable; 
		// map<Function*, vector<FnCall>> mapMapFunc;

		vector<qGateArg> qbitsInCurrentFunc; //qbits in function
		vector<qGateArg> qbitsInCurrentFuncShort; //qbits in function
		vector<qGateArg> qbitsInitInCurrentFunc; //new qbits declared in function
		vector<qGateArg> funcArgList; //function arguments
		vector<FnCall> fnCall;
		// vector<FnCall> mapFunction; //trace sequence of qgate calls
		map<Value*, qGateArg> mapInstRtn; //trace return cbits for Meas Inst
		
		map<string, BasicBlock *> basicBlockTagMap;
		/* If the block branches to more than one successors. */
		map<BasicBlock *, string> basicBlockCondTable;

		int btCount; //backtrace count

		GenQASM() : ModulePass(ID) {  }

		//analyze control flow
		void analyzeBasicBlock(Function* F);

		bool getQbitArrDim(Type* instType, qGateArg* qa);
		bool backtraceOperand(Value* opd, int opOrIndex, instType instOpcode);
		string backtraceCbit(Value* opd, int opOrIndex, instType instOpcode);
		void analyzeAllocInst(Function* F,Instruction* pinst);
		void analyzeAllocInstShort(Function* F,Instruction* pinst);

		void processStoreCbitInst(CallInst * pInst);
		void processCallInst(CallInst * pInst);
		void processConditionInst(BasicBlock * basicBlock, BranchInst * branchInst);

		// void analyzeCallInst(Function* F,Instruction* pinst);
		// void analyzeInst(Function* F,Instruction* pinst);
		void analyzeInst_block(BasicBlock* basicBlock, Instruction* pInst);

		//run - Print out SCCs in the call graph for the specified module.
		bool runOnModule(Module &M);

		void genQASM_REG(Function* F);
		void genQASM_block(BasicBlock * blockBlock);
		void genQASM(Function* F);
		void getFunctionArguments(Function* F);
		bool DetermineQFunc(Function* F);

		string to_string(int var);

		string printVarName(StringRef s){
			std::string sName = s.str();
			std::replace(sName.begin(), sName.end(), '.', '_');

			unsigned pos = sName.rfind("..");

			if(pos == sName.length()-2){
				std::string s1 = sName.substr(0,pos);
				return s1;
			}else{
				unsigned pos1 = sName.rfind(".");

				if(pos1 == sName.length()-1){
					std::string s1 = sName.substr(0,pos1);
					return s1;
				}else{
					pos = sName.find(".addr");
					std::string s1 = sName.substr(0,pos);     
					return s1;
				}
			}
    	}
    
		void print_qgateArg(qGateArg qg){
			if(qg.isUndef)
				errs() << " UNDEF ";
			else{
				if(qg.isQbit || qg.isCbit || qg.isAbit){
					errs() << printVarName(qg.argPtr->getName());
					if(!(qg.isPtr)){
						//if only single-dimensional qbit arrays expected
						//--if(qg.numDim == 0)
						//errs()<<"["<<qg.valOrIndex<<"]";
						//--else
						//if n-dimensional qbit arrays expected
						for(int ndim = 0; ndim < qg.numDim; ndim++)
							errs() << "[" << qg.dimSize[ndim] << "]";
					}
				}else{
					//assert(!qg.isPtr); //NOTE: not expecting non-quantum pointer variables as arguments to quantum functions. If they exist, then print out name of variable
					if(qg.isPtr) errs() << " UNRECOGNIZED ";
					else if(qg.isDouble) errs() << qg.val;
					else errs() << qg.valOrIndex;
				}
			}
		}

		void print_qgateArg_debug(qGateArg qg){
			errs() << "Printing QGate Argument:\n";
			if(qg.argPtr) errs() << "\tName: " << qg.argPtr->getName() << "\n";
			errs() << "\tArg Num: " << qg.argNum << "\n"
				<< "\tisUndef: " << qg.isUndef
				<< "\tisQbit: " << qg.isQbit
				<< "\tisAbit: " << qg.isAbit
				<< "\tisCbit: " << qg.isCbit
				<< "\tisPtr: " << qg.isPtr << "\n"
				<< "\tValue or Index: " << qg.valOrIndex << "\n"
				<< "\tNum of Dim: " << qg.numDim << "\n";
			for(int i = 0; i < qg.numDim; i++)
				errs() << "\tdimSize ["<<i<<"] = " << qg.dimSize[i] << "\n";
		}
		
		void print(raw_ostream &O, const Module* = 0) const { 
			errs() << "Qbits found: ";
			for(unsigned int vb=0; vb<vectQbit.size(); vb++){
				errs() << vectQbit[vb]->getName() <<" ";
			}
			errs()<<"\n";
		}
		//getAnalysisUsage - This pass requires the CallGraph.
		virtual void getAnalysisUsage(AnalysisUsage &AU) const {
			AU.setPreservesAll();
			AU.addRequired<CallGraph>();
		}
	};
}

char GenQASM::ID = 0;
static RegisterPass<GenQASM>
X("gen-openqasm", "Generate OpenQASM output code"); //spatil: should be Z or X??

bool GenQASM::backtraceOperand(Value* opd, int opOrIndex, instType instOpcode){
	if(instOpcode == call){
		if(opOrIndex == 0){	//backtrace for operand
			//search for opd in qbit/cbit vector
			std::vector<Value*>::iterator vIter=std::find(vectQbit.begin(),vectQbit.end(),opd);
			if(vIter != vectQbit.end()){
				if(debugGenOpenQASM)
					errs()<<"Found qubit associated: "<< opd->getName() << "\n";

				tmpDepQbit[0].argPtr = opd;

				return true;
			}

			if(btCount>MAX_BT_COUNT) return false;

			if(GetElementPtrInst *GEPI = dyn_cast<GetElementPtrInst>(opd)){
				if(debugGenOpenQASM){
					errs() << "Get Elem Ptr Inst Found: " << *GEPI << "\n";
					errs() << GEPI->getPointerOperand()->getName() << "\n";
					errs() << "\thas index = " << GEPI->hasIndices();
					errs() << "\thas all constant index = " << GEPI->hasAllConstantIndices() << "\n";
				}

				if(GEPI->hasAllConstantIndices()){
					Instruction* pInst = dyn_cast<Instruction>(opd);
					unsigned numOps = pInst->getNumOperands();
					if(debugGenOpenQASM)
						errs() << "\tHas constant index. Num Operands: " << numOps << ": ";

					bool foundOne = backtraceOperand(pInst->getOperand(0),0, call);

					if(numOps>2){ //set the dimensionality of the qbit
						tmpDepQbit[0].numDim = numOps-2;
					
						for(unsigned arrIter=2; arrIter < numOps; arrIter++){
							ConstantInt *CI = dyn_cast<ConstantInt>(pInst->getOperand(arrIter));
							//errs() << "Arr[ "<<arrIter<<" ] = "<<CI->getZExtValue()<<"\n";
							if(tmpDepQbit.size()==1){
								tmpDepQbit[0].dimSize[arrIter-2] = CI->getZExtValue();  
							}
						}
					}else if(numOps==2){
						tmpDepQbit[0].numDim = 1;
						ConstantInt *CI = dyn_cast<ConstantInt>(pInst->getOperand(numOps-1));
						if(tmpDepQbit.size()==1){
							tmpDepQbit[0].dimSize[0] = CI->getZExtValue();
							if(debugGenOpenQASM)
								errs()<<"\tFound constant index = "<<CI->getValue()<<"\n";
						}
					}

					//NOTE: getelemptr instruction can have multiple indices. Currently considering last operand as desired index for qubit. Check this reasoning. 
					ConstantInt *CI = dyn_cast<ConstantInt>(pInst->getOperand(numOps-1));
					if(tmpDepQbit.size()==1){
						tmpDepQbit[0].valOrIndex = CI->getZExtValue();
						if(debugGenOpenQASM)
							errs()<<"\tFound constant index = "<<CI->getValue()<<"\n";
					}
					return foundOne;
				}else if(GEPI->hasIndices()){ //NOTE: Edit this function for multiple indices, some of which are constant, others are not.
				
					errs() << "Oh no! I don't know how to handle this case..ABORT ABORT..\n";
					Instruction* pInst = dyn_cast<Instruction>(opd);
					unsigned numOps = pInst->getNumOperands();
					if(debugGenOpenQASM)
						errs() << "\tHas non-constant index. Num Operands: " << numOps << ": ";		
					bool foundOne = backtraceOperand(pInst->getOperand(0),0, call);

					if(tmpDepQbit[0].isQbit && !(tmpDepQbit[0].isPtr)){     
						//NOTE: getelemptr instruction can have multiple indices. consider last operand as desired index for qubit. Check if this is true for all.
						backtraceOperand(pInst->getOperand(numOps-1),1, call);
					}else if(tmpDepQbit[0].isAbit && !(tmpDepQbit[0].isPtr)){
						backtraceOperand(pInst->getOperand(numOps-1),1, call);
					}
					return foundOne;
				}else{
					Instruction* pInst = dyn_cast<Instruction>(opd);
					unsigned numOps = pInst->getNumOperands();
					bool foundOne = false;
					for(unsigned iop=0;(iop<numOps && !foundOne);iop++){
						foundOne = foundOne || backtraceOperand(pInst->getOperand(iop),0, call);
					}
					return foundOne;
				}
			}
			
			if(isa<LoadInst>(opd)){
				if(tmpDepQbit[0].isQbit && !tmpDepQbit[0].isPtr){
					tmpDepQbit[0].numDim = 1;
					tmpDepQbit[0].dimSize[0] = 0;
					if(debugGenOpenQASM)
						errs()<<"\tAdded default dim to qbit & not ptr variable.\n";
				}else if(tmpDepQbit[0].isAbit && !tmpDepQbit[0].isPtr){
					tmpDepQbit[0].numDim = 1;
					tmpDepQbit[0].dimSize[0] = 0;
				}
			}

			if(Instruction* pInst = dyn_cast<Instruction>(opd)){
				unsigned numOps = pInst->getNumOperands();
				bool foundOne = false;
				for(unsigned iop=0;(iop<numOps && !foundOne);iop++){
					btCount++;
					foundOne = foundOne || backtraceOperand(pInst->getOperand(iop),0, call);
					btCount--;
				}
				return foundOne;
			}else{
				if(debugGenOpenQASM) errs() << "Ending Recursion\n";
				return false;
			}
		}else if(opOrIndex == 1){ //opOrIndex == 1; i.e. Backtracing for Index    
			if(btCount>MAX_BT_COUNT) return true; //prevent infinite backtracing 

			if(ConstantInt *CI = dyn_cast<ConstantInt>(opd)){
				tmpDepQbit[0].valOrIndex = CI->getZExtValue();
				if(debugGenOpenQASM)
					errs() << "\tFound constant index = " << CI->getValue()<<"\n";
				return true;
			}    
			if(Instruction* pInst = dyn_cast<Instruction>(opd)){
				unsigned numOps = pInst->getNumOperands();
				bool foundOne = false;
				for(unsigned iop=0;(iop<numOps && !foundOne);iop++){
					btCount++;
					foundOne = foundOne || backtraceOperand(pInst->getOperand(iop),1, call);
					btCount--;
				}
				return foundOne;
			}
		}else{ //opOrIndex == 2: backtracing to call inst MeasZ
			if(debugGenOpenQASM)
				errs() << "backtracing for call inst: " << *opd << "\n";
			if(CallInst *endCI = dyn_cast<CallInst>(opd)){
				if(endCI->getCalledFunction()->getName().find("llvm.Meas") != string::npos){
					tmpDepQbit[0].argPtr = opd;

					if(debugGenOpenQASM)
						errs() << "\tFound call inst = " << *endCI << "\n";
					return true;
				}else{
					if(Instruction* pInst = dyn_cast<Instruction>(opd)){
						unsigned numOps = pInst->getNumOperands();
						bool foundOne=false;
						for(unsigned iop = 0; (iop < numOps && !foundOne); iop++){
							btCount++;
							foundOne = foundOne || backtraceOperand(pInst->getOperand(iop),2, call);
							btCount--;
						}
						return foundOne;
					}
				}
			}else{
				if(Instruction* pInst = dyn_cast<Instruction>(opd)){
					unsigned numOps = pInst->getNumOperands();
					bool foundOne=false;
					for(unsigned iop=0;(iop<numOps && !foundOne);iop++){
						btCount++;
						foundOne = foundOne || backtraceOperand(pInst->getOperand(iop),2, call);
						btCount--;
					}
					return foundOne;
				}
			}
		}
	}else if(instOpcode == br){
		if(AllocaInst * AI = dyn_cast<AllocaInst>(opd)){
			if(debugGenOpenQASM)
				errs() << "\tFound cbit associated: " << opd->getName() << "\n";
			return true;
		}else{
			///// operand index should case by case
			///// also, check if the operand is cbit
			if(debugGenOpenQASM)
				errs() << "\tbacktracing for br inst: " << *opd << "\n";
			Instruction * pInst = dyn_cast<Instruction> (opd);
			backtraceOperand(pInst->getOperand(0), 0, br);
			return true;
		}
	}

  	return false;
}

string GenQASM::backtraceCbit(Value* opd, int opOrIndex, instType instOpcode){
		if(AllocaInst * AI = dyn_cast<AllocaInst>(opd)){
			if(debugGenOpenQASM)
				errs() << "\tFound cbit associated: " << opd->getName() << "\n";
			return opd->getName();
		}else{
			///// operand index should case by case
			///// also, check if the operand is cbit
			if(debugGenOpenQASM)
				errs() << "\tbacktracing for br inst: " << *opd << "\n";
			Instruction * pInst = dyn_cast<Instruction> (opd);
			return backtraceCbit(pInst->getOperand(0), 0, br);
		}
}

bool GenQASM::getQbitArrDim(Type *instType, qGateArg* qa){
	bool myRet = false;

	errs() << "In get_all_dimensions\n";

	if(ArrayType *arrayType = dyn_cast<ArrayType>(instType)){
		Type *elementType = arrayType->getElementType();
		uint64_t arraySize = arrayType->getNumElements();
		errs() << "Array Size = " << arraySize << "\n";
		qa->dimSize[qa->numDim] = arraySize;
		qa->numDim++;

		if(elementType->isIntegerTy(16)){
			myRet = true;
			qa->isQbit = true;
		}else if(elementType->isIntegerTy(1)){
			myRet = true;
			qa->isCbit = true;
		}else if(elementType->isIntegerTy(8)){
			myRet = true;
			qa->isAbit = true;
		}else if(elementType->isArrayTy()){
			myRet |= getQbitArrDim(elementType,qa);
		}else myRet = false;
	}
	return myRet;
}

void GenQASM::analyzeAllocInstShort(Function* F, Instruction* pInst){

	if(AllocaInst *AI = dyn_cast<AllocaInst>(pInst)){
		Type *allocatedType = AI->getAllocatedType();

		if(ArrayType *arrayType = dyn_cast<ArrayType>(allocatedType)){      
			qGateArg tmpQArg;

			Type *elementType = arrayType->getElementType();
			if(elementType->isIntegerTy(16)){
				if(debugGenOpenQASM)
					errs() << "\tNew QBit Allocation Found: " << AI->getName() << "\n";
				qbitsInCurrentFuncShort.push_back(tmpQArg);
			}else if(elementType->isIntegerTy(1)){
				if(debugGenOpenQASM)
					errs() << "\tNew CBit Allocation Found: " << AI->getName() << "\n";
				qbitsInCurrentFuncShort.push_back(tmpQArg);
			}else if(elementType->isIntegerTy(8)){
				qbitsInCurrentFuncShort.push_back(tmpQArg);
			}
		}else if(allocatedType->isIntegerTy(16)){
			qGateArg tmpQArg;
			qbitsInCurrentFuncShort.push_back(tmpQArg);
		}else if(allocatedType->isIntegerTy(8)){
			qGateArg tmpQArg;
			qbitsInCurrentFuncShort.push_back(tmpQArg);
		}
		//find argName2 in funcArgList - avoid printing out qbit declaration twice
		//std::map<Function*, vector<qGateArg> >::iterator mIter = funcArgList.find(F);
		//if(mIter != funcArgList.end()){
		return;
	}
}

void GenQASM::analyzeAllocInst(Function * F, Instruction * pInst){
	if (AllocaInst *AI = dyn_cast<AllocaInst>(pInst)){
		Type *allocatedType = AI->getAllocatedType();
		if(ArrayType *arrayType = dyn_cast<ArrayType>(allocatedType)){
			qGateArg tmpQArg;
			Type *elementType = arrayType->getElementType();
			uint64_t arraySize = arrayType->getNumElements();
			if (elementType->isIntegerTy(16)){
				if(debugGenOpenQASM)
					errs() << "\tNew QBit Allocation Found: " << AI->getName() <<"\n";
				vectQbit.push_back(AI);
				tmpQArg.isQbit = true;
				tmpQArg.argPtr = AI;
				tmpQArg.numDim = 1;
				tmpQArg.dimSize[0] = arraySize;
				tmpQArg.valOrIndex = arraySize;
				//(qbitsInCurrentFunc.find(F))->second.push_back(tmpQArg);
				qbitsInCurrentFunc.push_back(tmpQArg);
				//(qbitsInitInCurrentFunc.find(F))->second.push_back(tmpQArg);	
				qbitsInitInCurrentFunc.push_back(tmpQArg);	
			}else if(elementType->isIntegerTy(1)){
				if(debugGenOpenQASM)
					errs() << "\tNew CBit Allocation Found: " << AI->getName() <<"\n";
				vectQbit.push_back(AI); //Cbit added here
				tmpQArg.isCbit = true;
				tmpQArg.argPtr = AI;
				tmpQArg.numDim = 1;
				tmpQArg.dimSize[0] = arraySize;
				tmpQArg.valOrIndex = arraySize;
				//(qbitsInCurrentFunc.find(F))->second.push_back(tmpQArg);
				qbitsInCurrentFunc.push_back(tmpQArg);
				//(qbitsInitInCurrentFunc.find(F))->second.push_back(tmpQArg);	
				qbitsInitInCurrentFunc.push_back(tmpQArg);	
			}else if(elementType->isIntegerTy(8)){
				vectQbit.push_back(AI); //Cbit added here
				tmpQArg.isCbit = false;
				tmpQArg.isAbit = true;
				tmpQArg.argPtr = AI;
				tmpQArg.numDim = 1;
				tmpQArg.dimSize[0] = arraySize;
				tmpQArg.valOrIndex = arraySize;
				//(qbitsInCurrentFunc.find(F))->second.push_back(tmpQArg);
				qbitsInCurrentFunc.push_back(tmpQArg);
				//(qbitsInitInCurrentFunc.find(F))->second.push_back(tmpQArg);	
				qbitsInitInCurrentFunc.push_back(tmpQArg);	
			}else if(elementType->isArrayTy()){
				errs() << "Multidimensional array\n";

				tmpQArg.dimSize[0] = arraySize;
				tmpQArg.numDim++;
				tmpQArg.valOrIndex = arraySize;

				//recurse on multi-dimensional array
				bool isQAlloc = getQbitArrDim(elementType,&tmpQArg);

				if(isQAlloc){
					vectQbit.push_back(AI);
					tmpQArg.argPtr = AI;
					//(qbitsInCurrentFunc.find(F))->second.push_back(tmpQArg);
					qbitsInCurrentFunc.push_back(tmpQArg);
					//(qbitsInitInCurrentFunc.find(F))->second.push_back(tmpQArg);
					qbitsInitInCurrentFunc.push_back(tmpQArg);

					if(debugGenOpenQASM)
						print_qgateArg_debug(tmpQArg);
				}	  
      		}
		}else if(allocatedType->isIntegerTy(16)){
			qGateArg tmpQArg;
			if(debugGenOpenQASM) 
				errs() << "Found New Qbit Allocation \n";
			vectQbit.push_back(AI);
			tmpQArg.isQbit = true;
			tmpQArg.argPtr = AI;
			tmpQArg.numDim = 1;
			//tmpQArg.dimSize[0] = 1;
			tmpQArg.dimSize[0] = cast<ConstantInt>(AI->getArraySize())->getSExtValue();
			tmpQArg.valOrIndex = 1;
			qbitsInCurrentFunc.push_back(tmpQArg);
			qbitsInitInCurrentFunc.push_back(tmpQArg);
		}else if(allocatedType->isPointerTy()){
		
			/*Note: this is necessary if -mem2reg is not run on LLVM IR before.
			Eg without -mem2reg
			module(i8* %q){
			%q.addr = alloca i8*, align 8
			...
			}
			qbit q.addr must be mapped to argument q. Hence the following code.
			If it is known that -O1 will be run, then this can be removed.
			*/
		
			Type *elementType = allocatedType->getPointerElementType();
			if (elementType->isIntegerTy(16)){
				vectQbit.push_back(AI);
				
				qGateArg tmpQArg;
				tmpQArg.isPtr = true;
				tmpQArg.isQbit = true;
				tmpQArg.argPtr = AI;
				
				//(qbitsInCurrentFunc.find(F))->second.push_back(tmpQArg);
				qbitsInCurrentFunc.push_back(tmpQArg);
				
				std::string argName = AI->getName();
				unsigned pos = argName.find(".addr");
				std::string argName2 = argName.substr(0,pos);

				//find argName2 in funcArgList - avoid printing out qbit declaration twice
				//std::map<Function*, vector<qGateArg> >::iterator mIter = funcArgList.find(F);
				//if(mIter != funcArgList.end()){
				bool foundit = false;
				for(vector<qGateArg>::iterator vParamIter = funcArgList.begin();(vParamIter!=funcArgList.end() && !foundit);++vParamIter){
					if((*vParamIter).argPtr->getName() == argName2){ 
						foundit = true;
					}
				}
				if(!foundit) //do not add duplicate declaration	    
					qbitsInitInCurrentFunc.push_back(tmpQArg);
			}else if(elementType->isIntegerTy(8)){
				vectQbit.push_back(AI);
				qGateArg tmpQArg;
				tmpQArg.isPtr = true;
				tmpQArg.isAbit = true;
				tmpQArg.argPtr = AI;

				qbitsInCurrentFunc.push_back(tmpQArg);

				std::string argName = AI->getName();
				unsigned pos = argName.find(".addr");
				std::string argName2 = argName.substr(0,pos);
				bool foundit = false;
				for(vector<qGateArg>::iterator vParamIter = funcArgList.begin();(vParamIter!=funcArgList.end() && !foundit);++vParamIter){
					if((*vParamIter).argPtr->getName() == argName2) foundit = true;
				}
				if(!foundit) qbitsInitInCurrentFunc.push_back(tmpQArg);
			}
		}
    return;
  	}
}

// void GenQASM::analyzeCallInst(Function* F, Instruction* pInst){

// 	if(CallInst *CI = dyn_cast<CallInst>(pInst)){

// 		if(debugGenOpenQASM)
// 			errs() << "--Analyze Call Inst:" << CI->getCalledFunction()->getName() << "\n";
		
// 		//Instruction: call void @store_cbit(i1 %0, i1 * %1) nounwind
// 		if(CI->getCalledFunction()->getName() == "store_cbit"){
// 			qGateArg tempMeasureValue_;
// 			tempMeasureValue_.isCbit = true;
// 			tmpDepQbit.push_back(tempMeasureValue_);
// 			backtraceOperand(CI->getArgOperand(0), 2, call);
// 			Value * rtnVal = tmpDepQbit[0].argPtr;
// 			tmpDepQbit.clear();

// 			qGateArg tmpCbit_;
// 			tmpCbit_.isCbit = true;
// 			tmpCbit_.isPtr = true;
// 			tmpDepQbit.push_back(tmpCbit_);
// 			backtraceOperand(CI->getArgOperand(1), 0, call);
// 			mapInstRtn[rtnVal] = tmpDepQbit[0];

// 			tmpDepQbit.clear();

// 			return;

// 		}
		
// 		bool tracked_all_operands = true;
		
// 		for(unsigned iop = 0; iop < CI->getNumArgOperands(); iop++){
// 			tmpDepQbit.clear();

// 			qGateArg tmpQGateArg;
// 			btCount=0;

// 			if(debugGenOpenQASM)
// 				errs() << "Call inst operand num: " << iop << "\n";

// 			tmpQGateArg.argNum = iop;

// 			if(isa<UndefValue>(CI->getArgOperand(iop))){
// 				//errs() << "WARNING: LLVM IR code has UNDEF values. \n";
// 				tmpQGateArg.isUndef = true;	
// 				//exit(1);
// 				//assert(0 && "LLVM IR code has UNDEF values. Aborting...");
// 			}

// 			Type* argType = CI->getArgOperand(iop)->getType();
// 			if(argType->isPointerTy()){
// 				tmpQGateArg.isPtr = true;
// 				Type *argElemType = argType->getPointerElementType();
// 				if(argElemType->isIntegerTy(16)) tmpQGateArg.isQbit = true;
// 				if(argElemType->isIntegerTy(1)) tmpQGateArg.isCbit = true;
// 				if(argElemType->isIntegerTy(8)) tmpQGateArg.isAbit = true;
// 			}else if(argType->isIntegerTy(16)){
// 				tmpQGateArg.isQbit = true;
// 				tmpQGateArg.valOrIndex = 0;	 
// 			}else if(argType->isIntegerTy(32)){
// 				if(ConstantInt *CInt = dyn_cast<ConstantInt>(CI->getArgOperand(iop))){
// 					tmpQGateArg.isParam = true;
// 					tmpQGateArg.valOrIndex = CInt->getZExtValue();
// 				}
// 			}else if(argType->isIntegerTy(8)){
// 				tmpQGateArg.isAbit = true;
// 				tmpQGateArg.valOrIndex = 0;
// 			}else if(argType->isIntegerTy(1)){
// 				tmpQGateArg.isCbit = true;
// 				tmpQGateArg.valOrIndex = 0;	 
// 			}	  	

// 			//check if argument is constant int	
// 			if(ConstantInt *CInt = dyn_cast<ConstantInt>(CI->getArgOperand(iop))){
// 				tmpQGateArg.valOrIndex = CInt->getZExtValue();
// 				if(debugGenOpenQASM)
// 					errs() << "\tFound constant argument = " << CInt->getValue() << "\n";
// 			}

// 			//check if argument is constant float	
// 			if(ConstantFP *CFP = dyn_cast<ConstantFP>(CI->getArgOperand(iop))){
// 				tmpQGateArg.val = CFP->getValueAPF().convertToDouble();
// 				tmpQGateArg.isDouble = true;
// 				if(debugGenOpenQASM){
// 					errs()<<"\tCall Inst = "<<*CI<<"\n";
// 					errs()<<"\tFound constant double argument = "<<tmpQGateArg.val<<"\n";
// 				}
// 			}

// 			tmpDepQbit.push_back(tmpQGateArg);

// 			tracked_all_operands &= backtraceOperand(CI->getArgOperand(iop),0, call);

// 			if(tmpDepQbit.size()>0){
// 				if(debugGenOpenQASM) print_qgateArg_debug(tmpDepQbit[0]);
				
// 				allDepQbit.push_back(tmpDepQbit[0]);
// 				assert(tmpDepQbit.size() == 1 && "tmpDepQbit SIZE GT 1");
// 				tmpDepQbit.clear();
// 			}
// 		}
					
// 		//form info packet
// 		FnCall qInfo;
// 		qInfo.func = CI->getCalledFunction();
// 		qInfo.instPtr = CI;
		
// 		if(allDepQbit.size() > 0){
// 			if(debugGenOpenQASM){
// 				errs() << "Call inst: " << CI->getCalledFunction()->getName();	    
// 				errs() << ": Found all arguments: ";       
// 				for(unsigned int vb=0; vb<allDepQbit.size(); vb++){
// 					if(allDepQbit[vb].argPtr)
// 						errs() << allDepQbit[vb].argPtr->getName() << " ";
// 					else
// 						errs() << allDepQbit[vb].valOrIndex << " ";
// 				}
// 				errs() << "\n";
// 			}

// 			//populate vector of passed qubit arguments
// 			for(unsigned int vb = 0; vb < allDepQbit.size(); vb++)
// 				qInfo.qArgs.push_back(allDepQbit[vb]);
// 		}
		
// 		//map<Function*, vector<FnCall> >::iterator mvdpit = mapFunction.find(F);	
// 		//(*mvdpit).second.push_back(qInfo);      
// 		mapFunction.push_back(qInfo);
// 		return;      
//     }
// }

void GenQASM::processStoreCbitInst(CallInst * CI){
	if(debugGenOpenQASM)
		errs() << "--analyze store_cbit inst--" << "\n";

	qGateArg tempMeasureValue_;
	tempMeasureValue_.isCbit = true;
	tmpDepQbit.push_back(tempMeasureValue_);
	backtraceOperand(CI->getArgOperand(0), 2, call);
	Value * rtnVal = tmpDepQbit[0].argPtr;
	tmpDepQbit.clear();

	qGateArg tmpCbit_;
	tmpCbit_.isCbit = true;
	tmpCbit_.isPtr = true;
	tmpDepQbit.push_back(tmpCbit_);
	backtraceOperand(CI->getArgOperand(1), 0, call);
	mapInstRtn[rtnVal] = tmpDepQbit[0];

	tmpDepQbit.clear();

	return;
}

void GenQASM::processCallInst(CallInst * callInst){
	bool tracked_all_operands = true;
	
	for(unsigned iop = 0; iop < callInst->getNumArgOperands(); iop++){
		tmpDepQbit.clear();

		qGateArg tmpQGateArg;
		btCount=0;

		if(debugGenOpenQASM)
			errs() << "Call inst operand num: " << iop << "\n";

		tmpQGateArg.argNum = iop;

		if(isa<UndefValue>(callInst->getArgOperand(iop))){
			//errs() << "WARNING: LLVM IR code has UNDEF values. \n";
			tmpQGateArg.isUndef = true;	
			//exit(1);
			//assert(0 && "LLVM IR code has UNDEF values. Aborting...");
		}

		Type* argType = callInst->getArgOperand(iop)->getType();
		if(argType->isPointerTy()){
			tmpQGateArg.isPtr = true;
			Type *argElemType = argType->getPointerElementType();
			if(argElemType->isIntegerTy(16)) tmpQGateArg.isQbit = true;
			if(argElemType->isIntegerTy(1)) tmpQGateArg.isCbit = true;
			if(argElemType->isIntegerTy(8)) tmpQGateArg.isAbit = true;
		}else if(argType->isIntegerTy(16)){
			tmpQGateArg.isQbit = true;
			tmpQGateArg.valOrIndex = 0;	 
		}else if(argType->isIntegerTy(32)){
			if(ConstantInt *CInt = dyn_cast<ConstantInt>(callInst->getArgOperand(iop))){
				tmpQGateArg.isParam = true;
				tmpQGateArg.valOrIndex = CInt->getZExtValue();
			}
		}else if(argType->isIntegerTy(8)){
			tmpQGateArg.isAbit = true;
			tmpQGateArg.valOrIndex = 0;
		}else if(argType->isIntegerTy(1)){
			tmpQGateArg.isCbit = true;
			tmpQGateArg.valOrIndex = 0;	 
		}	  	

		//check if argument is constant int	
		if(ConstantInt *CInt = dyn_cast<ConstantInt>(callInst->getArgOperand(iop))){
			tmpQGateArg.valOrIndex = CInt->getZExtValue();
			if(debugGenOpenQASM)
				errs() << "\tFound constant argument = " << CInt->getValue() << "\n";
		}

		//check if argument is constant float	
		if(ConstantFP *CFP = dyn_cast<ConstantFP>(callInst->getArgOperand(iop))){
			tmpQGateArg.val = CFP->getValueAPF().convertToDouble();
			tmpQGateArg.isDouble = true;
			if(debugGenOpenQASM){
				errs()<<"\tCall Inst = "<<*callInst<<"\n";
				errs()<<"\tFound constant double argument = "<<tmpQGateArg.val<<"\n";
			}
		}

		tmpDepQbit.push_back(tmpQGateArg);

		tracked_all_operands &= backtraceOperand(callInst->getArgOperand(iop),0, call);

		if(tmpDepQbit.size()>0){
			if(debugGenOpenQASM) print_qgateArg_debug(tmpDepQbit[0]);
			
			allDepQbit.push_back(tmpDepQbit[0]);
			assert(tmpDepQbit.size() == 1 && "tmpDepQbit SIZE GT 1");
			tmpDepQbit.clear();
		}
	}
				
	//form info packet
	FnCall qInfo;
	qInfo.func = callInst->getCalledFunction();
	qInfo.instPtr = callInst;
	
	if(allDepQbit.size() > 0){
		if(debugGenOpenQASM){
			errs() << "Call inst: " << callInst->getCalledFunction()->getName();	    
			errs() << ": Found all arguments: ";       
			for(unsigned int vb=0; vb<allDepQbit.size(); vb++){
				if(allDepQbit[vb].argPtr)
					errs() << allDepQbit[vb].argPtr->getName() << " ";
				else
					errs() << allDepQbit[vb].valOrIndex << " ";
			}
			errs() << "\n";
		}

		//populate vector of passed qubit arguments
		for(unsigned int vb = 0; vb < allDepQbit.size(); vb++)
			qInfo.qArgs.push_back(allDepQbit[vb]);
	}
	
	//map<Function*, vector<FnCall> >::iterator mvdpit = mapFunction.find(F);	
	//(*mvdpit).second.push_back(qInfo);      
	fnCall.push_back(qInfo);
	return;
}

void GenQASM::processConditionInst(BasicBlock * basicBlock, BranchInst* branchInst){

		if(branchInst->getNumOperands() == 3){
			if(debugGenOpenQASM)
				errs() << "--analyze condition inst--" << "\n";
			///// check if the condition is related to cbit
			if(debugGenOpenQASM)
				errs() << "Branch condition: " << "\n";
			string cbitCond = backtraceCbit(branchInst->getOperand(0), 2, br);
			basicBlockCondTable[basicBlock] = cbitCond;

			///// get if then block
			if(debugGenOpenQASM)
				errs() << "If then block: " << branchInst->getOperand(2)->getName() << "\n";
			///// get if end block
			if(debugGenOpenQASM)
				errs() << "If end block: " << branchInst->getOperand(1)->getName() << "\n";
		}
	return;
}


// void GenQASM::analyzeInst(Function* F, Instruction* pInst){
// 	if(debugGenOpenQASM)
// 		errs() << "\nProcessing Inst: "<< *pInst << "\n";

// 	if(debugGenOpenQASM){
// 		errs() << "\tOpcode: "<< pInst->getOpcodeName() << "\n";

// 		unsigned numOps = pInst->getNumOperands();
// 		errs() << "\tNum Operands: " << numOps << ";\n";
// 		// for(unsigned iop = 0; iop < numOps; iop++){
// 		// 	errs() << pInst->getOperand(iop)->getName() << "; ";
// 		// }
// 		// errs() << "\n";		
// 	}

// 	analyzeCallInst(F, pInst);


// 	return;
// }

void GenQASM::analyzeInst_block(BasicBlock* basicBlock, Instruction* pInst){
	if(debugGenOpenQASM)
		errs() << "\nProcessing Inst: "<< *pInst << "\n";

	if(debugGenOpenQASM){
		errs() << "\tOpcode: "<< pInst->getOpcodeName() << "\n";

		unsigned numOps = pInst->getNumOperands();
		errs() << "\tNum Operands: " << numOps << ";\n";
	}

	if(CallInst * CI = dyn_cast<CallInst>(pInst)){
		if(CI->getCalledFunction()->getName() == "store_cbit"){
			processStoreCbitInst(CI);
		}else{
			processCallInst(CI);
		}
	}else if(BranchInst *BI = dyn_cast<BranchInst>(pInst)){
		processConditionInst(basicBlock, BI);
	}

	return;
}

std::string GenQASM::to_string(int var){
	stringstream ss; 
	ss << var;
	return ss.str();
}

void GenQASM::genQASM_REG(Function* F){
	//print qbits declared in function
	for(vector<qGateArg>::iterator vvit=qbitsInitInCurrentFunc.begin(),vvitE=qbitsInitInCurrentFunc.end();vvit!=vvitE;++vvit){
		std::string qName = (*vvit).argPtr->getName();
		std::replace(qName.begin(), qName.end(), '.','_');
		if((*vvit).isQbit)
			errs() << "qreg " <<printVarName(qName);
		if((*vvit).isCbit)
			errs() << "creg " <<printVarName(qName);
		if((*vvit).isAbit)
			errs() << "qreg " <<printVarName(qName);

		//if only single-dimensional qbit arrays expected
		//errs()<<"["<<(*vvit).valOrIndex<<"];\n ";

		//if n-dimensional qbit arrays expected
		for(int ndim = 0; ndim < (*vvit).numDim; ndim++)
			errs()<<"["<<(*vvit).dimSize[ndim]<<"]";
		errs() << ";\n";
	}
}

void GenQASM::genQASM_block(BasicBlock * blockBlock){
	vector<FnCall> fnCallList = fnCallTable.find(blockBlock)->second;

	for(unsigned mIndex = 0; mIndex < fnCallList.size(); mIndex++){
		// If the FuncCall is related to quantum operation
		if(fnCallList[mIndex].qArgs.size()>0){
			string fToPrint = fnCallList[mIndex].func->getName();
			if(fToPrint.find("llvm.") != string::npos) fToPrint = fToPrint.substr(5);

			//MeasX, PrepZ/X, and Fredkin require some special works, so we handle them separately
			//NB(pranav): a better way to handle these would be to decompose MeasX, PrepZ/X,
			//and Fredkin in terms of the other gates during an earlier LLVM pass

			if(fToPrint.find("MeasX") != string::npos){
				errs()<<"h ";
				print_qgateArg(fnCallList[mIndex].qArgs.front());
				errs()<<";\n";

				fToPrint = "MeasZ";
			}

			if(fToPrint.find("MeasZ") != string::npos){
				errs()<<"measure ";
				print_qgateArg(fnCallList[mIndex].qArgs.front());
				errs()<<" -> ";

				//get inst ptr
				Value* thisInstPtr = fnCallList[mIndex].instPtr;
				//find inst in mapInstRtn
				map<Value*, qGateArg>::iterator mvq = mapInstRtn.find(thisInstPtr);
				if(mvq!=mapInstRtn.end()){
					errs()<<printVarName(((*mvq).second).argPtr->getName());
					if(((*mvq).second).isPtr)
					errs()<<"["<<((*mvq).second).valOrIndex<<"]";
				}
				errs()<<";\n";
				continue;
			}

			if(fToPrint.find("Prep") != string::npos) {
				errs()<<"reset ";
				print_qgateArg(fnCallList[mIndex].qArgs.front());
				errs()<<";\n";

				//For preparation to |1> state, apply a bit flip after reset to get 0->1
				if(fnCallList[mIndex].qArgs.back().valOrIndex == 1) {
					errs()<<"x ";
					print_qgateArg(fnCallList[mIndex].qArgs.front());
					errs()<<";\n";
				}
				//For preparation in X basis, change basis from Z basis with H gate
				if(fToPrint.find("PrepX") != string::npos) {
					errs()<<"h ";
					print_qgateArg(fnCallList[mIndex].qArgs.front());
					errs()<<";\n";
				}
				continue;
			}

			if(fToPrint.find("Fredkin") != string::npos) {
				//OpenQASM doesn't have Fredkin gate, so we decompose into CNOTs and Toffoli with identity
				//Fredkin(q0, q1, q2) = (I ⊗ CNOT(q1, q2)) * Toffoli(q0, q2, q1) * (I ⊗ CNOT(q1, q2))

				//CNOT(second input, third input)
				errs()<<"cx ";
				print_qgateArg(fnCallList[mIndex].qArgs[1]);
				errs()<<", ";
				print_qgateArg(fnCallList[mIndex].qArgs[2]);
				errs()<<";\n";

				//Toffoli(first input, third input, second input)
				errs()<<"ccx ";
				print_qgateArg(fnCallList[mIndex].qArgs[0]);
				errs()<<", ";
				print_qgateArg(fnCallList[mIndex].qArgs[1]);
				errs()<<", ";
				print_qgateArg(fnCallList[mIndex].qArgs[2]);
				errs()<<";\n";

				//CNOT(second input, third input)
				errs()<<"cx ";
				print_qgateArg(fnCallList[mIndex].qArgs[1]);
				errs()<<", ";
				print_qgateArg(fnCallList[mIndex].qArgs[2]);
				errs()<<";\n";

				continue;
			}

			if(fToPrint.find("CNOT") != string::npos) fToPrint = "cx";
			else if(fToPrint.find("Toffoli.") != string::npos) fToPrint = "ccx";
			else if(fToPrint.find("H.i") != string::npos) fToPrint = "h";
			else if(fToPrint.substr(0,2) == "Rx") fToPrint = "rx";
			else if(fToPrint.substr(0,2) == "Ry") fToPrint = "ry";
			else if(fToPrint.substr(0,2) == "Rz") fToPrint = "rz";
			else if(fToPrint.find("S.") != string::npos) fToPrint = "s";
			else if(fToPrint.find("T.") != string::npos) fToPrint = "t";
			else if(fToPrint.find("Sdag") != string::npos) fToPrint = "sdg";
			else if(fToPrint.find("Tdag") != string::npos) fToPrint = "tdg";
			else if(fToPrint.find("X.") != string::npos) fToPrint = "x";
			else if(fToPrint.find("Z.") != string::npos) fToPrint = "z";


			std::replace(fToPrint.begin(), fToPrint.end(), '.', '_');
			std::replace(fToPrint.begin(), fToPrint.end(), '-', '_');

			if(fToPrint.find("rx") != string::npos || fToPrint.find("ry") != string::npos || fToPrint.find("rz") != string::npos) {
				qGateArg angleArg = fnCallList[mIndex].qArgs.back();
				fnCallList[mIndex].qArgs.pop_back();
				errs()<<fToPrint<<"(";
				print_qgateArg(angleArg);
				errs()<<") ";
			}else{
				errs()<<fToPrint<<" ";
			}

			//print all but last argument
			for(vector<qGateArg>::iterator vpIt=fnCallList[mIndex].qArgs.begin(), vpItE=fnCallList[mIndex].qArgs.end();vpIt!=vpItE-1;++vpIt){
				print_qgateArg(*vpIt);
				errs()<<",";
			}
			print_qgateArg(fnCallList[mIndex].qArgs.back());
			errs()<<";\n";
    	}
    }

	map<BasicBlock *, string>::iterator hit = basicBlockCondTable.find(blockBlock);
	if(basicBlockCondTable.end()!= hit){
		errs() << "if(" << hit->second << " == 1) ";
	}

	return ;
}

///// genQASM should run on basicblock
// void GenQASM::genQASM(Function* F){
// 	//map<Function*, vector<qGateArg> >::iterator mpItr;
// 	//map<Function*, vector<qGateArg> >::iterator mpItr2;
// 	//map<Function*, vector<qGateArg> >::iterator mvpItr;
// 	//mpItr = qbitsInCurrentFunc.find(F);
// 	//if(qbitsInCurrentFunc.size()>0){
    
// 	/* Get FnCall vector of the function. */
//     mapFunction = mapMapFunc.find(F)->second; 
//     //print gates in function
//     //map<Function*, vector<FnCall> >::iterator mfvIt = mapFunction.find(F);
//     for(unsigned mIndex = 0; mIndex < mapFunction.size(); mIndex++){
// 		// If the FuncCall is related to quantum operation
// 		if(mapFunction[mIndex].qArgs.size()>0){
// 			string fToPrint = mapFunction[mIndex].func->getName();
// 			if(fToPrint.find("llvm.") != string::npos) fToPrint = fToPrint.substr(5);

// 			//MeasX, PrepZ/X, and Fredkin require some special works, so we handle them separately
// 			//NB(pranav): a better way to handle these would be to decompose MeasX, PrepZ/X,
// 			//and Fredkin in terms of the other gates during an earlier LLVM pass

// 			if(fToPrint.find("MeasX") != string::npos){
// 				errs()<<"h ";
// 				print_qgateArg(mapFunction[mIndex].qArgs.front());
// 				errs()<<";\n";

// 				fToPrint = "MeasZ";
// 			}

// 			if(fToPrint.find("MeasZ") != string::npos){
// 				errs()<<"measure ";
// 				print_qgateArg(mapFunction[mIndex].qArgs.front());
// 				errs()<<" -> ";

// 				//get inst ptr
// 				Value* thisInstPtr = mapFunction[mIndex].instPtr;
// 				//find inst in mapInstRtn
// 				map<Value*, qGateArg>::iterator mvq = mapInstRtn.find(thisInstPtr);
// 				if(mvq!=mapInstRtn.end()){
// 					errs()<<printVarName(((*mvq).second).argPtr->getName());
// 					if(((*mvq).second).isPtr)
// 					errs()<<"["<<((*mvq).second).valOrIndex<<"]";
// 				}
// 				errs()<<";\n";
// 				continue;
// 			}

// 			if(fToPrint.find("Prep") != string::npos) {
// 				errs()<<"reset ";
// 				print_qgateArg(mapFunction[mIndex].qArgs.front());
// 				errs()<<";\n";

// 				//For preparation to |1> state, apply a bit flip after reset to get 0->1
// 				if(mapFunction[mIndex].qArgs.back().valOrIndex == 1) {
// 					errs()<<"x ";
// 					print_qgateArg(mapFunction[mIndex].qArgs.front());
// 					errs()<<";\n";
// 				}
// 				//For preparation in X basis, change basis from Z basis with H gate
// 				if(fToPrint.find("PrepX") != string::npos) {
// 					errs()<<"h ";
// 					print_qgateArg(mapFunction[mIndex].qArgs.front());
// 					errs()<<";\n";
// 				}
// 				continue;
// 			}

// 			if(fToPrint.find("Fredkin") != string::npos) {
// 				//OpenQASM doesn't have Fredkin gate, so we decompose into CNOTs and Toffoli with identity
// 				//Fredkin(q0, q1, q2) = (I ⊗ CNOT(q1, q2)) * Toffoli(q0, q2, q1) * (I ⊗ CNOT(q1, q2))

// 				//CNOT(second input, third input)
// 				errs()<<"cx ";
// 				print_qgateArg(mapFunction[mIndex].qArgs[1]);
// 				errs()<<", ";
// 				print_qgateArg(mapFunction[mIndex].qArgs[2]);
// 				errs()<<";\n";

// 				//Toffoli(first input, third input, second input)
// 				errs()<<"ccx ";
// 				print_qgateArg(mapFunction[mIndex].qArgs[0]);
// 				errs()<<", ";
// 				print_qgateArg(mapFunction[mIndex].qArgs[1]);
// 				errs()<<", ";
// 				print_qgateArg(mapFunction[mIndex].qArgs[2]);
// 				errs()<<";\n";

// 				//CNOT(second input, third input)
// 				errs()<<"cx ";
// 				print_qgateArg(mapFunction[mIndex].qArgs[1]);
// 				errs()<<", ";
// 				print_qgateArg(mapFunction[mIndex].qArgs[2]);
// 				errs()<<";\n";

// 				continue;
// 			}

// 			if(fToPrint.find("CNOT") != string::npos) fToPrint = "cx";
// 			else if(fToPrint.find("Toffoli.") != string::npos) fToPrint = "ccx";
// 			else if(fToPrint.find("H.i") != string::npos) fToPrint = "h";
// 			else if(fToPrint.substr(0,2) == "Rx") fToPrint = "rx";
// 			else if(fToPrint.substr(0,2) == "Ry") fToPrint = "ry";
// 			else if(fToPrint.substr(0,2) == "Rz") fToPrint = "rz";
// 			else if(fToPrint.find("S.") != string::npos) fToPrint = "s";
// 			else if(fToPrint.find("T.") != string::npos) fToPrint = "t";
// 			else if(fToPrint.find("Sdag") != string::npos) fToPrint = "sdg";
// 			else if(fToPrint.find("Tdag") != string::npos) fToPrint = "tdg";
// 			else if(fToPrint.find("X.") != string::npos) fToPrint = "x";
// 			else if(fToPrint.find("Z.") != string::npos) fToPrint = "z";


// 			std::replace(fToPrint.begin(), fToPrint.end(), '.', '_');
// 			std::replace(fToPrint.begin(), fToPrint.end(), '-', '_');

// 			if(fToPrint.find("rx") != string::npos || fToPrint.find("ry") != string::npos || fToPrint.find("rz") != string::npos) {
// 				qGateArg angleArg = mapFunction[mIndex].qArgs.back();
// 				mapFunction[mIndex].qArgs.pop_back();
// 				errs()<<fToPrint<<"(";
// 				print_qgateArg(angleArg);
// 				errs()<<") ";
// 			}else{
// 				errs()<<fToPrint<<" ";
// 			}

// 			//print all but last argument
// 			for(vector<qGateArg>::iterator vpIt=mapFunction[mIndex].qArgs.begin(), vpItE=mapFunction[mIndex].qArgs.end();vpIt!=vpItE-1;++vpIt){
// 				print_qgateArg(*vpIt);
// 				errs()<<",";
// 			}
// 			print_qgateArg(mapFunction[mIndex].qArgs.back());
// 			errs()<<";\n";
//     	}
//     }
//     //errs() << "//--//-- End Fn: " << F->getName() << " --//--// \n";
// }


bool GenQASM::DetermineQFunc(Function* F)
{
    for(inst_iterator instIb = inst_begin(F),instIe=inst_end(F); instIb!=instIe;++instIb){
        Instruction *pInst = &*instIb; //Grab pointer to instruction reference	      
	    analyzeAllocInstShort(F,pInst);
	}
    if(qbitsInCurrentFuncShort.size() > 0) return true;
    qbitsInCurrentFuncShort.clear();
    return false;
}

void GenQASM::getFunctionArguments(Function* F){
	//std::vector<unsigned> qGateArgs;
	for(Function::arg_iterator ait=F->arg_begin();ait!=F->arg_end();++ait){    
		std::string argName = (ait->getName()).str();
		Type* argType = ait->getType();
		unsigned int argNum=ait->getArgNo();         

		qGateArg tmpQArg;
		tmpQArg.argPtr = ait;
		tmpQArg.argNum = argNum;

		if(argType->isPointerTy()){
			if(debugGenOpenQASM) errs()<<"Argument Type: " << *argType <<"\n";
			
			tmpQArg.isPtr = true;

			Type *elementType = argType->getPointerElementType();
			if(elementType->isIntegerTy(16)){
				tmpQArg.isQbit = true;
				vectQbit.push_back(ait);
				qbitsInCurrentFunc.push_back(tmpQArg);
				funcArgList.push_back(tmpQArg);
			}else if(elementType->isIntegerTy(1)){
				tmpQArg.isCbit = true;
				vectQbit.push_back(ait);
				qbitsInCurrentFunc.push_back(tmpQArg);
				funcArgList.push_back(tmpQArg);
			}else if(elementType->isIntegerTy(8)){
				tmpQArg.isAbit = true;
				vectQbit.push_back(ait);
				qbitsInCurrentFunc.push_back(tmpQArg);
				funcArgList.push_back(tmpQArg);
			}else if(argType->isIntegerTy(16)){
				tmpQArg.isQbit = true;
				vectQbit.push_back(ait);
				qbitsInCurrentFunc.push_back(tmpQArg);
				funcArgList.push_back(tmpQArg);
			}else if(argType->isIntegerTy(32)){
				tmpQArg.isParam = true;
				vectQbit.push_back(ait);
				funcArgList.push_back(tmpQArg);
			}else if(argType->isIntegerTy(1)){
				tmpQArg.isCbit = true;
				vectQbit.push_back(ait);
				qbitsInCurrentFunc.push_back(tmpQArg);
				funcArgList.push_back(tmpQArg);
			}else if(argType->isIntegerTy(8)){
				tmpQArg.isAbit = true;
				vectQbit.push_back(ait);
				qbitsInCurrentFunc.push_back(tmpQArg);
				funcArgList.push_back(tmpQArg);
			}else if(argType->isDoubleTy())
				funcArgList.push_back(tmpQArg);

			if(debugGenOpenQASM) print_qgateArg_debug(tmpQArg);
		}
	}
}

//run - Find datapaths for qubits
bool GenQASM::runOnModule(Module &M) {
	vector<Function*> qFuncs;

	unsigned sccNum = 0;

	errs() << "OPENQASM 2.0;\n";
	errs() << "include \"qelib1.inc\";\n";

	CallGraphNode* rootNode1 = getAnalysis<CallGraph>().getRoot();

	sccNum = 0;

	for (scc_iterator<CallGraphNode*> sccIb = scc_begin(rootNode1),
			E = scc_end(rootNode1); sccIb != E; ++sccIb){

		const std::vector<CallGraphNode*> &nextSCC = *sccIb;

		if(debugGenOpenQASM) 
			errs() << "\nSCC #" << ++sccNum << " : ";      

		for (std::vector<CallGraphNode*>::const_iterator nsccI = nextSCC.begin(),
				E = nextSCC.end(); nsccI != E; ++nsccI){

			Function *F = (*nsccI)->getFunction();	  
		
			if(F && !F->isDeclaration()){
				if(debugGenOpenQASM)
					errs() << "Processing Function:" << F->getName() <<" \n ";

				//Initialize map structures for this function.
				//vector<qGateArg> myQIFVec, myQIFVec1, myQIFVec2;
				qbitsInCurrentFunc.clear();
				qbitsInitInCurrentFunc.clear();
				funcArgList.clear();

				//std::vector<FnCall> myFuncMapVec;
				// mapFunction.clear();

				getFunctionArguments(F);
				
				/* Iterate through all the blocks in the function. */
				for(Function::iterator BB = F->begin(), BBend = F->end(); BB != BBend; ++BB){
					BasicBlock* pBB = BB;
					if(debugGenOpenQASM)
						errs() << "\nProcessing BasicBlock: " << pBB->getName() << "\n";
					/* Build basic block label map. */
					basicBlockTagMap.insert(make_pair(pBB->getName(), pBB));
					
					/* Iterate through all the instructions in the block and find all the alloc inst. */
					for(BasicBlock::iterator instIb = pBB->begin(), instIe = pBB->end(); instIb != instIe; ++instIb){
						Instruction * pInst = &*instIb;
						if(debugGenOpenQASM)
							errs() << "\n\tProcessing Inst: " << *pInst << "\n";
						analyzeAllocInst(F,pInst);
					}
				}

				/* Process Quantum Function. */
				//map<Function*, vector<qGateArg> >::iterator mpItr = qbitsInCurrentFunc.find(F);
				if(qbitsInCurrentFunc.size()>0){
					mapQbitsInit.insert(make_pair(F, qbitsInitInCurrentFunc));
					mapFuncArgs.insert(make_pair(F, funcArgList));
					qFuncs.push_back(F);

					for(Function::iterator BB = F->begin(), BBend = F->end(); BB != BBend; ++BB){
						BasicBlock * basicBlock = BB;
						if(debugGenOpenQASM)
							errs() << "\n\n--Processing BasicBlock: " << basicBlock->getName() << "\n";

						fnCall.clear();

						for(BasicBlock::iterator instIb = basicBlock->begin(), instIe = basicBlock->end(); instIb != instIe; ++instIb){
							Instruction *pInst = &*instIb;  
							allDepQbit.clear();

							analyzeInst_block(basicBlock, pInst);
							
						}
						fnCallTable.insert(make_pair(basicBlock, fnCall));
					}
					// mapMapFunc.insert(make_pair(F, mapFunction));
				}
			}else{
				if(debugGenOpenQASM)
					errs() << "WARNING: Ignoring external node or dummy function.";
			}
		}
		if(nextSCC.size() == 1 && sccIb.hasLoop())
			errs() << " (Has self-loop).";
	}

	bool hasMain = false;
	for(vector<Function*>::iterator it = qFuncs.begin(); it!=qFuncs.end(); it++){
		if ((*it)->getName() == "main") hasMain = true;
	}

	vector<Function*>::iterator lastItPos;
	if(!hasMain){
		lastItPos = qFuncs.end();
		lastItPos--;
	}

	for(vector<Function*>::iterator it = qFuncs.begin(); it != qFuncs.end(); it++){
		/////another for loop to iterate basic block 
		std::string newName = (*it)->getName();
		if(newName.find("CNOT") != string::npos) newName = "CNOT";
		else if(newName.find("NOT.") != string::npos) newName = "X";
		else if(newName.find("Toffoli.") != string::npos) newName = "Toffoli";
		else if(newName.find("MeasX") != string::npos) newName = "MeasX";
		else if(newName.find("MeasZ") != string::npos) newName = "MeasZ";
		else if(newName.find("H.i") != string::npos) newName = "H";
		else if(newName.find("PrepX") != string::npos) newName = "PrepX";
		else if(newName.find("PrepZ") != string::npos) newName = "PrepZ";
		else if(newName.substr(0,2) == "Rx") newName = "Rx";
		else if(newName.substr(0,2) == "Ry") newName = "Ry";
		else if(newName.substr(0,2) == "Rz") newName = "Rz";
		else if(newName.find("S.") != string::npos) newName = "S";
		else if(newName.find("T.") != string::npos) newName = "T";
		else if(newName.find("Sdag") != string::npos) newName = "Sdag";
		else if(newName.find("Tdag") != string::npos) newName = "Tdag";
		else if(newName.find("X.") != string::npos) newName = "X";
		else if(newName.find("Z.") != string::npos) newName = "Z";

		std::replace(newName.begin(), newName.end(), '.', '_');

		(*it)->setName(newName);
		genQASM_REG((*it));
		//genQASM((*it));

		for(Function::iterator BB = (*it)->begin(), BBend = (*it)->end(); BB != BBend; ++BB){
			BasicBlock * pBB = BB;
			genQASM_block(pBB);
		}
	}
	errs() << "\n";
	return false;
}
