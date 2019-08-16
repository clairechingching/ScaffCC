//===- GenOpenQASM.cpp - Generate OpenQASM output -----------===//
//
//         The LLVM Scaffold Compiler Infrastructure
//
// This file was created by Scaffold Compiler Working Group
//
//===--------------------------------------------------------===//

#include <sstream>
#include <numeric>
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

#define MAX_BACKTRACE_COUNT 150 //max number of backtrace allowed (avoid infinite recursive backtrace)
#define MAX_QBIT_ARR_DIM 50 //max dimensions allowed for qbit arrays

/* Set true if debug mode. */
bool debugGenOpenQASM = true;

namespace{

	enum argType{
		/* Quantum Type. */
		qbit,
		cbit,
		/* Classical Type. */
		intVal,
		doubleVal,
		/* Not defined. */
		undef
	};

	/* Non-general case for backtraceoperand. */
	enum backtraceExp{
		cmpConstant,
		ptrToArray,
		nonExp
	};

	struct dataRepresentation{
		Value * instPtr;
		argType type;
		bool isPtr;
		vector<int> index; // in the reverse order
		vector<int> dimSize; // sizes of dimensions vector

		/* Classical Inst. */
		int intValue;
		double doubValue;
		bool isClassical(){
			if(type == intVal || type == doubleVal) return true; else return false;
		}
		string val(){
			stringstream ss;
			if(type == intVal) ss << " " << intValue << " ";
			if(type == doubleVal) ss << " " << doubValue << " ";
			return ss.str();
		}
		/* Quantum Inst. */
		bool isqbit(){
			if(type == qbit) return true; else return false;
		}
		bool iscbit(){
			if(type == cbit) return true; else return false;
		}
		void printQRegisterName(){
			switch(type){
				case undef:
					errs() << " UNDEF ";
					break;
				case qbit:
				case cbit:
					errs() << getName();
					break;
				default:
					errs() << " error ";
					break;
			}
		}
		string qbitVarString(){
			stringstream ss;
			ss << getName();
			if(index.size() > 1){
				for(unsigned i = index.size()-1; i > 0; i--)
					ss << "_" << index[i];
			}
				ss << "[" << to_string(index[0]) << "]";
			return ss.str();
		}
		string cbitVarString(){
			stringstream ss;
			ss << getName();
			for(unsigned i = 0; i < index.size(); i++){
				ss << "_" << index[i];
			}
			ss << "[0]";
			return ss.str();
		}
		/* Used in conditional statement, since OpenQASM only support array-wise measurement. */
		string cbitArrayString(){
			stringstream ss;
			ss << getName();
			for(unsigned i = 0; i < index.size(); i++){
				ss << "_" << index[i];
			}
			return ss.str();
		}

		dataRepresentation() : instPtr(NULL), type(undef), isPtr(false), index({}), dimSize({}){}

		string getName(){ return instPtr->getName(); }
		
		void printDebugMode(){
			if(isClassical()){
				/* Printing Classical Value. */
				errs() << "\t\tPrinting Constant: ";
				if(type == intVal) errs() << intValue << "\n";
				if(type == doubleVal) errs() << doubValue << "\n";
			}else{
				errs() << "\t\tPrinting Quantum Register:\n";
				errs() << "\t\tName: ";
				printQRegisterName();
				errs() << "\n";
				errs() << "\t\tType: ";
				switch(type){
					case undef:
						errs() << "UNDEF\n";
						break;
					case qbit:
						errs() << "qubit\n";
						break;
					case cbit:
						errs() << "cbit\n";
						break;
					default:
						errs() << "error\n";
						break;
				}
				errs() << "\t\tSize: ";
				for(unsigned i = 0; i < dimSize.size(); i++){
					errs() << "[" << dimSize[i] << "]";
				}
				errs() << "\n";
				errs() << "\t\tIndex: ";
				if(index.size() == 0) errs() << "Not applied.\n";
				for(unsigned i = 0; i < index.size(); i++){
					errs() << "[" << index[i] << "]";
				}
				errs() << "\n";
			}
		}
	};
	
	/* Datapath Sequence. */
	struct FnCall{
		Function* func;
		Value* instPtr;
		std::vector<dataRepresentation> qArgs_;
	};

	struct CondCall{
		Value* instPtr;
		std::vector<dataRepresentation> qArgs_;
	};

	argType quantumRegisterSetupHelper(dataRepresentation * qRegister, Type * type){
		if(type->isIntegerTy(16)){
			return qbit;
		}else if(type->isIntegerTy(1)){
			return cbit;
		}else if(type->isArrayTy()){
			ArrayType * arrayType = dyn_cast<ArrayType>(type);
			qRegister->dimSize.push_back(arrayType->getNumElements());
			return quantumRegisterSetupHelper(qRegister, arrayType->getElementType());
		}else if(type->isPointerTy()){
			////// Pending...
			if(!(qRegister->isPtr)) qRegister->isPtr = true;
			return quantumRegisterSetupHelper(qRegister, type->getPointerElementType());
		}else{
			return undef;
		}
	}

	void quantumRegisterSetup(dataRepresentation * qRegister){
		AllocaInst * AI = dyn_cast<AllocaInst>(qRegister->instPtr);
		Type * allocatedType = AI->getAllocatedType();
		qRegister->type = quantumRegisterSetupHelper(qRegister, allocatedType);
	}

	void classicalRegisterSetup(dataRepresentation * cRegister){
		if(cRegister->instPtr == NULL){
			return;
		}else if(ConstantInt * CInt = dyn_cast<ConstantInt>(cRegister->instPtr)){
			cRegister->type = intVal;
			cRegister->intValue = CInt->getSExtValue();
			return;
		}else if(ConstantFP * CFP = dyn_cast<ConstantFP>(cRegister->instPtr)){
			cRegister->type = doubleVal;
			cRegister->doubValue = CFP->getValueAPF().convertToDouble();
			return;
		}else{
			errs() << "Unhandled Case!\n";
			return;
		};

	}

	bool isAllocQuantumType(Type * allocatedType){
		if(allocatedType->isIntegerTy(16)){
			return true;
		}else if(allocatedType->isIntegerTy(1)){
			return true;
		}else if(ArrayType * arrayType = dyn_cast<ArrayType>(allocatedType)){
			return isAllocQuantumType(arrayType->getElementType());
		}else{
			return false;
		}
	}

	struct GenQASM : public ModulePass {
		/* Pass Identification, Replacement for typeid. */
		static char ID;

		std::vector<dataRepresentation> tmpDepQbit_;
		std::vector<dataRepresentation> allDepQbit_;
		
		map<BasicBlock *, vector<FnCall>> fnCallTable; 
		map<Function *, vector<dataRepresentation>> mapQbitsInit_;
		map<Function *, vector<dataRepresentation>> mapFuncArgs_;

		vector<dataRepresentation> qbitsInCurrentFunc_;
		vector<dataRepresentation> qbitsInitInCurrentFunc_;
		vector<dataRepresentation> funcArgList_;

		vector<FnCall> fnCall;

		map<Value*, dataRepresentation> mapInstRtn_;

		/* If the block branches to more than one successors. */
		map<BasicBlock *, vector<dataRepresentation>> basicBlockCondTable;

		int backtraceCount;

		GenQASM() : ModulePass(ID) {  }

		dataRepresentation backtraceOperand(Value * operand, backtraceExp exp);
		void backtraceOperand_helper(dataRepresentation * datRepPtr, Value * operand, int gettingIndex, backtraceExp exp);
		
		void analyzeAllocInst(Function* F,Instruction* pinst);
		void analyzeInst_block(BasicBlock* basicBlock, Instruction* pInst);

		void processStoreCbitInst(CallInst * pInst);
		void processCallInst(CallInst * pInst);
		void processConditionInst(BasicBlock * basicBlock, BranchInst * branchInst);

		void getFunctionArguments(Function* F);

		/* Run - Print out SCCs in the call graph for the module. */
		bool runOnModule(Module &M);

		void genQASM_REG(Function* F);
		void genQASM_block(BasicBlock * blockBlock);


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
    
		// void print_qgateArg(qGateArg qg){
		// 	if(qg.isUndef)
		// 		errs() << " UNDEF ";
		// 	else{
		// 		if(qg.isQbit || qg.isCbit || qg.isAbit){
		// 			errs() << printVarName(qg.argPtr->getName());
		// 			if(!(qg.isPtr)){
		// 				//if only single-dimensional qbit arrays expected
		// 				//--if(qg.numDim == 0)
		// 				//errs()<<"["<<qg.valOrIndex<<"]";
		// 				//--else
		// 				//if n-dimensional qbit arrays expected
		// 				for(int ndim = 0; ndim < qg.numDim; ndim++)
		// 					errs() << "[" << qg.dimSize[ndim] << "]";
		// 			}
		// 		}else{
		// 			//assert(!qg.isPtr); //NOTE: not expecting non-quantum pointer variables as arguments to quantum functions. If they exist, then print out name of variable
		// 			if(qg.isPtr) errs() << " UNRECOGNIZED ";
		// 			else if(qg.isDouble) errs() << qg.val;
		// 			else errs() << qg.valOrIndex;
		// 		}
		// 	}
		// }

		/* getAnalysisUsage - Requires the CallGraph. */
		virtual void getAnalysisUsage(AnalysisUsage &AU) const {
			AU.setPreservesAll();
			AU.addRequired<CallGraph>();
		}
	};
}

char GenQASM::ID = 0;
static RegisterPass<GenQASM>
X("gen-openqasm", "Generate OpenQASM output code"); //spatil: should be Z or X??

// bool GenQASM::backtraceOperand(Value* opd, int opOrIndex){

// 	if(opOrIndex == 0){	//backtrace for operand
// 		//search for opd in qbit/cbit vector
// 		std::vector<Value*>::iterator vIter=std::find(vectQbit.begin(),vectQbit.end(),opd);
// 		if(vIter != vectQbit.end()){
// 			tmpDepQbit[0].argPtr = opd;
// 			return true;
// 		}

// 		if(backtraceCount>MAX_BACKTRACE_COUNT) return false;

// 		if(GetElementPtrInst *GEPI = dyn_cast<GetElementPtrInst>(opd)){

// 			if(GEPI->hasAllConstantIndices()){
// 				Instruction* pInst = dyn_cast<Instruction>(opd);
// 				unsigned numOps = pInst->getNumOperands();

// 				bool foundOne = backtraceOperand(pInst->getOperand(0),0);

// 				if(numOps>2){ //set the dimensionality of the qbit
// 					tmpDepQbit[0].numDim = numOps-2;
				
// 					for(unsigned arrIter=2; arrIter < numOps; arrIter++){
// 						ConstantInt *CI = dyn_cast<ConstantInt>(pInst->getOperand(arrIter));
// 						//errs() << "Arr[ "<<arrIter<<" ] = "<<CI->getZExtValue()<<"\n";
// 						if(tmpDepQbit.size()==1){
// 							tmpDepQbit[0].dimSize[arrIter-2] = CI->getZExtValue();  
// 						}
// 					}
// 				}else if(numOps==2){
// 					tmpDepQbit[0].numDim = 1;
// 					ConstantInt *CI = dyn_cast<ConstantInt>(pInst->getOperand(numOps-1));
// 					if(tmpDepQbit.size()==1){
// 						tmpDepQbit[0].dimSize[0] = CI->getZExtValue();
// 					}
// 				}

// 				//NOTE: getelemptr instruction can have multiple indices. Currently considering last operand as desired index for qubit. Check this reasoning. 
// 				ConstantInt *CI = dyn_cast<ConstantInt>(pInst->getOperand(numOps-1));
// 				if(tmpDepQbit.size()==1){
// 					tmpDepQbit[0].valOrIndex = CI->getZExtValue();
// 				}
// 				return foundOne;
// 			}else if(GEPI->hasIndices()){ //NOTE: Edit this function for multiple indices, some of which are constant, others are not.
			
// 				errs() << "Oh no! I don't know how to handle this case..ABORT ABORT..\n";
// 				Instruction* pInst = dyn_cast<Instruction>(opd);
// 				unsigned numOps = pInst->getNumOperands();
// 				if(debugGenOpenQASM)
// 					errs() << "\tHas non-constant index. Num Operands: " << numOps << ": ";		
// 				bool foundOne = backtraceOperand(pInst->getOperand(0),0);

// 				if(tmpDepQbit[0].isQbit && !(tmpDepQbit[0].isPtr)){     
// 					//NOTE: getelemptr instruction can have multiple indices. consider last operand as desired index for qubit. Check if this is true for all.
// 					backtraceOperand(pInst->getOperand(numOps-1),1);
// 				}else if(tmpDepQbit[0].isAbit && !(tmpDepQbit[0].isPtr)){
// 					backtraceOperand(pInst->getOperand(numOps-1),1);
// 				}
// 				return foundOne;
// 			}else{
// 				Instruction* pInst = dyn_cast<Instruction>(opd);
// 				unsigned numOps = pInst->getNumOperands();
// 				bool foundOne = false;
// 				for(unsigned iop=0;(iop<numOps && !foundOne);iop++){
// 					foundOne = foundOne || backtraceOperand(pInst->getOperand(iop),0);
// 				}
// 				return foundOne;
// 			}
// 		}
		
// 		if(isa<LoadInst>(opd)){
// 			if(tmpDepQbit[0].isQbit && !tmpDepQbit[0].isPtr){
// 				tmpDepQbit[0].numDim = 1;
// 				tmpDepQbit[0].dimSize[0] = 0;
// 				//Added default dim to qbit & not ptr variable.
// 			}else if(tmpDepQbit[0].isAbit && !tmpDepQbit[0].isPtr){
// 				tmpDepQbit[0].numDim = 1;
// 				tmpDepQbit[0].dimSize[0] = 0;
// 			}
// 		}

// 		if(Instruction* pInst = dyn_cast<Instruction>(opd)){
// 			unsigned numOps = pInst->getNumOperands();
// 			bool foundOne = false;
// 			for(unsigned iop=0;(iop<numOps && !foundOne);iop++){
// 				backtraceCount++;
// 				foundOne = foundOne || backtraceOperand(pInst->getOperand(iop),0);
// 				backtraceCount--;
// 			}
// 			return foundOne;
// 		}else{
 
// 			return false;
// 		}
// 	}else if(opOrIndex == 1){ //opOrIndex == 1; i.e. Backtracing for Index    
// 		if(backtraceCount>MAX_BACKTRACE_COUNT) return true; //prevent infinite backtracing 

// 		if(ConstantInt *CI = dyn_cast<ConstantInt>(opd)){
// 			tmpDepQbit[0].valOrIndex = CI->getZExtValue();
// 			return true;
// 		}    
// 		if(Instruction* pInst = dyn_cast<Instruction>(opd)){
// 			unsigned numOps = pInst->getNumOperands();
// 			bool foundOne = false;
// 			for(unsigned iop=0;(iop<numOps && !foundOne);iop++){
// 				backtraceCount++;
// 				foundOne = foundOne || backtraceOperand(pInst->getOperand(iop),1);
// 				backtraceCount--;
// 			}
// 			return foundOne;
// 		}
// 	}else{ //opOrIndex == 2: backtracing to call inst MeasZ
// 		if(CallInst *endCI = dyn_cast<CallInst>(opd)){
// 			if(endCI->getCalledFunction()->getName().find("llvm.Meas") != string::npos){
// 				tmpDepQbit[0].argPtr = opd;
// 				return true;
// 			}else{
// 				if(Instruction* pInst = dyn_cast<Instruction>(opd)){
// 					unsigned numOps = pInst->getNumOperands();
// 					bool foundOne=false;
// 					for(unsigned iop = 0; (iop < numOps && !foundOne); iop++){
// 						backtraceCount++;
// 						foundOne = foundOne || backtraceOperand(pInst->getOperand(iop),2);
// 						backtraceCount--;
// 					}
// 					return foundOne;
// 				}
// 			}
// 		}else{
// 			if(Instruction* pInst = dyn_cast<Instruction>(opd)){
// 				unsigned numOps = pInst->getNumOperands();
// 				bool foundOne=false;
// 				for(unsigned iop=0;(iop<numOps && !foundOne);iop++){
// 					backtraceCount++;
// 					foundOne = foundOne || backtraceOperand(pInst->getOperand(iop),2);
// 					backtraceCount--;
// 				}
// 				return foundOne;
// 			}
// 		}
// 	}
//   	return false;
// }

void GenQASM::backtraceOperand_helper(dataRepresentation * datRepPtr, Value * operand, int gettingIndex, backtraceExp exp){

	if(AllocaInst * AI = dyn_cast<AllocaInst>(operand)){
		if(debugGenOpenQASM)
			errs() << "\n\t\tAlloca inst Found: " << *AI << "\n";
		datRepPtr->instPtr = AI;
		return;

	}else if(GetElementPtrInst * GEPI = dyn_cast<GetElementPtrInst>(operand)){
		if(debugGenOpenQASM)
			errs() << "\n\t\tGetElemPtr inst Found: " << *GEPI << "\n";
		/* Get index. */
		if(GEPI->getNumOperands() == 3){
			if(exp == ptrToArray){
				ConstantInt * CInt = dyn_cast<ConstantInt>(GEPI->getOperand(2));
				int index = CInt->getSExtValue();
				if(debugGenOpenQASM) errs() << "\t\t[" << gettingIndex << "] Index: " << index << "\n";
				backtraceOperand_helper(datRepPtr, GEPI->getOperand(0), gettingIndex, exp);
			}else{
				ConstantInt * CInt = dyn_cast<ConstantInt>(GEPI->getOperand(2));
				int index = CInt->getSExtValue();
				if(debugGenOpenQASM) errs() << "\t\t[" << gettingIndex << "] Index: " << index << "\n";
				datRepPtr->index.push_back(index);
				backtraceOperand_helper(datRepPtr, GEPI->getOperand(0), gettingIndex, exp);
			}
			return;
		}else if(GEPI->getNumOperands() == 2){
			ConstantInt * CInt = dyn_cast<ConstantInt>(GEPI->getOperand(1));
			int index = CInt->getSExtValue();
			if(debugGenOpenQASM) errs() << "\t\t[" << gettingIndex << "] Index: " << index << "\n";
			datRepPtr->index.push_back(index);
			backtraceOperand_helper(datRepPtr, GEPI->getOperand(0), gettingIndex, ptrToArray);
		}else{
			errs() << "UNHANDLED GEPI CASE, BOOOOOOOOOO!\n";
		}
		return;
	}else if(CallInst * CI = dyn_cast<CallInst>(operand)){
		if(debugGenOpenQASM)
			errs() << "\n\t\tCall inst Found: " << *CI << "\n";
		if(CI->getCalledFunction()->getName().find("llvm.Meas") != string::npos){
			/////Pending...
			if(debugGenOpenQASM) errs() << "\n\t\tBACKTRACE OPERAND QUBIT: \n";
			backtraceOperand_helper(datRepPtr, CI->getOperand(0), gettingIndex, exp);
			// dataRepresentation qubit = backtraceOperand_(CI->getOperand(0));
			// datRepPtr->instPtr = operand;
		}
		return;
	}else if(PtrToIntInst * PTTI = dyn_cast<PtrToIntInst>(operand)){
		if(debugGenOpenQASM)
			errs() << "\n\t\tPtrToInt inst Found: " << *PTTI << "\n";
		backtraceOperand_helper(datRepPtr, PTTI->getOperand(0), 0, exp);
		return;
	}else if(ConstantInt * CInt = dyn_cast<ConstantInt>(operand)){
		datRepPtr->instPtr = CInt;
		if(debugGenOpenQASM) errs() << "\n\t\tInt Constant Found: " << CInt->getSExtValue() << "\n";
		return;
	}else if(ConstantFP * CFP = dyn_cast<ConstantFP>(operand)){
		datRepPtr->instPtr = CFP;
		if(debugGenOpenQASM) errs() << "\n\t\tDouble Constant Found: " << CFP->getValueAPF().convertToDouble() << "\n";
		return;
	}else if(LoadInst * LI = dyn_cast<LoadInst>(operand)){
		if(debugGenOpenQASM) errs() << "\n\t\tLoad inst Found: " << *LI << "\n";
		if(exp == cmpConstant){
			if(debugGenOpenQASM) errs() << "\n\t\tCmp constant is 1.\n";
			datRepPtr->type = intVal;
			datRepPtr->intValue = 1;
			return;
		}else{
			backtraceOperand_helper(datRepPtr, LI->getOperand(0), 0, exp);
			return;
		}
	}else if(CmpInst * CMPI = dyn_cast<CmpInst>(operand)){
		if(debugGenOpenQASM) errs() << "\n\t\tCompare inst Found: " << *CMPI << "\n";
		if(exp == cmpConstant){
			backtraceOperand_helper(datRepPtr, CMPI->getOperand(1), 0, exp);
		}else{
			backtraceOperand_helper(datRepPtr, CMPI->getOperand(0), 0, exp);
		}
		return;
	}else if(ZExtInst * ZEI = dyn_cast<ZExtInst>(operand)){
		if(debugGenOpenQASM) errs() << "\n\t\tZExt inst Found: " << *ZEI << "\n";
		backtraceOperand_helper(datRepPtr, ZEI->getOperand(0), 0, exp);
		return;
	}else if(isa<UndefValue>(operand)){
		datRepPtr->type = undef;
		if(debugGenOpenQASM) errs() << "Undef Inst: " << *operand << "\n";
		return;
	}else{
		if(debugGenOpenQASM) errs() << "UNHANDLED CASE, BOOOOOOOOOO! Inst: " << *operand << "\n";
		return;
	}
}

dataRepresentation GenQASM::backtraceOperand(Value * operand, backtraceExp exp){

	dataRepresentation returnDR;
	int gettingIndex = 0;

	backtraceOperand_helper(&returnDR, operand, gettingIndex, exp);
	
	return returnDR;
}

void GenQASM::analyzeAllocInst(Function * F, Instruction * pInst){
	if (AllocaInst *AI = dyn_cast<AllocaInst>(pInst)){
		Type * allocatedType_ = AI->getAllocatedType();

		if(isAllocQuantumType(allocatedType_)){

			if(debugGenOpenQASM) errs() << "\tNew qubit allocation: " << AI->getName() << "\n";

			dataRepresentation qRegister;
			qRegister.instPtr = AI;
			quantumRegisterSetup(&qRegister);
			
			if(debugGenOpenQASM) qRegister.printDebugMode();

			//qubits/new qubits in function
			qbitsInCurrentFunc_.push_back(qRegister);
			qbitsInitInCurrentFunc_.push_back(qRegister);

		}

		// Type *allocatedType = AI->getAllocatedType();
		// if(ArrayType *arrayType = dyn_cast<ArrayType>(allocatedType)){
		// 	qGateArg tmpQArg;
		// 	Type *elementType = arrayType->getElementType();
		// 	uint64_t arraySize = arrayType->getNumElements();
		// 	if (elementType->isIntegerTy(16)){

		// 		vectQbit.push_back(AI);
		// 		tmpQArg.isQbit = true;
		// 		tmpQArg.argPtr = AI;
		// 		tmpQArg.numDim = 1;
		// 		tmpQArg.dimSize[0] = arraySize;
		// 		tmpQArg.valOrIndex = arraySize;
				
		// 		qbitsInCurrentFunc.push_back(tmpQArg);
		// 		qbitsInitInCurrentFunc.push_back(tmpQArg);	
		// 	}else if(elementType->isIntegerTy(1)){

		// 		vectQbit.push_back(AI); //Cbit added here
		// 		tmpQArg.isCbit = true;
		// 		tmpQArg.argPtr = AI;
		// 		tmpQArg.numDim = 1;
		// 		tmpQArg.dimSize[0] = arraySize;
		// 		tmpQArg.valOrIndex = arraySize;
				
		// 		qbitsInCurrentFunc.push_back(tmpQArg);	
		// 		qbitsInitInCurrentFunc.push_back(tmpQArg);	
		// 	}else if(elementType->isIntegerTy(8)){

		// 		vectQbit.push_back(AI); //Cbit added here
		// 		tmpQArg.isCbit = false;
		// 		tmpQArg.isAbit = true;
		// 		tmpQArg.argPtr = AI;
		// 		tmpQArg.numDim = 1;
		// 		tmpQArg.dimSize[0] = arraySize;
		// 		tmpQArg.valOrIndex = arraySize;
				
		// 		qbitsInCurrentFunc.push_back(tmpQArg);
		// 		qbitsInitInCurrentFunc.push_back(tmpQArg);	

		// 	}else if(elementType->isArrayTy()){

		// 		tmpQArg.dimSize[0] = arraySize;
		// 		tmpQArg.numDim++;
		// 		tmpQArg.valOrIndex = arraySize;

		// 		bool isQAlloc = getQbitArrDim(elementType,&tmpQArg);

		// 		if(isQAlloc){
		// 			vectQbit.push_back(AI);
		// 			tmpQArg.argPtr = AI;
					
		// 			qbitsInCurrentFunc.push_back(tmpQArg);
		// 			qbitsInitInCurrentFunc.push_back(tmpQArg);
		// 		}	  
      	// 	}
		// }else if(allocatedType->isIntegerTy(16)){

		// 	qGateArg tmpQArg;
		// 	vectQbit.push_back(AI);
		// 	tmpQArg.isQbit = true;
		// 	tmpQArg.argPtr = AI;
		// 	tmpQArg.numDim = 1;

		// 	tmpQArg.dimSize[0] = cast<ConstantInt>(AI->getArraySize())->getSExtValue();
		// 	tmpQArg.valOrIndex = 1;
		// 	qbitsInCurrentFunc.push_back(tmpQArg);
		// 	qbitsInitInCurrentFunc.push_back(tmpQArg);

		// }else if(allocatedType->isPointerTy()){
		
		// 	/*Note: this is necessary if -mem2reg is not run on LLVM IR before.
		// 	Eg without -mem2reg
		// 	module(i8* %q){
		// 	%q.addr = alloca i8*, align 8
		// 	...
		// 	}
		// 	qbit q.addr must be mapped to argument q. Hence the following code.
		// 	If it is known that -O1 will be run, then this can be removed.
		// 	*/
		
		// 	Type *elementType = allocatedType->getPointerElementType();
		// 	if (elementType->isIntegerTy(16)){
		// 		vectQbit.push_back(AI);
				
		// 		qGateArg tmpQArg;
		// 		tmpQArg.isPtr = true;
		// 		tmpQArg.isQbit = true;
		// 		tmpQArg.argPtr = AI;
				
		// 		//(qbitsInCurrentFunc.find(F))->second.push_back(tmpQArg);
		// 		qbitsInCurrentFunc.push_back(tmpQArg);
				
		// 		std::string argName = AI->getName();
		// 		unsigned pos = argName.find(".addr");
		// 		std::string argName2 = argName.substr(0,pos);

		// 		//find argName2 in funcArgList - avoid printing out qbit declaration twice
		// 		//std::map<Function*, vector<qGateArg> >::iterator mIter = funcArgList.find(F);
		// 		//if(mIter != funcArgList.end()){
		// 		bool foundit = false;
		// 		for(vector<qGateArg>::iterator vParamIter = funcArgList.begin();(vParamIter!=funcArgList.end() && !foundit);++vParamIter){
		// 			if((*vParamIter).argPtr->getName() == argName2){ 
		// 				foundit = true;
		// 			}
		// 		}
		// 		if(!foundit) //do not add duplicate declaration	    
		// 			qbitsInitInCurrentFunc.push_back(tmpQArg);
		// 	}else if(elementType->isIntegerTy(8)){
		// 		vectQbit.push_back(AI);
		// 		qGateArg tmpQArg;
		// 		tmpQArg.isPtr = true;
		// 		tmpQArg.isAbit = true;
		// 		tmpQArg.argPtr = AI;

		// 		qbitsInCurrentFunc.push_back(tmpQArg);

		// 		std::string argName = AI->getName();
		// 		unsigned pos = argName.find(".addr");
		// 		std::string argName2 = argName.substr(0,pos);
		// 		bool foundit = false;
		// 		for(vector<qGateArg>::iterator vParamIter = funcArgList.begin();(vParamIter!=funcArgList.end() && !foundit);++vParamIter){
		// 			if((*vParamIter).argPtr->getName() == argName2) foundit = true;
		// 		}
		// 		if(!foundit) qbitsInitInCurrentFunc.push_back(tmpQArg);
		// 	}
		// }
    return;
  	}
}

void GenQASM::processStoreCbitInst(CallInst * CI){
	//if(debugGenOpenQASM) errs() << "\n\t\tBACKTRACE OPERAND MEASURE : \n";
	///// assert
	Value * rtnVal_ = CI->getArgOperand(0);
	tmpDepQbit_.clear();

	if(debugGenOpenQASM) errs() << "\n\t\tBACKTRACE OPERAND CBIT: \n";
	dataRepresentation cbit = backtraceOperand(CI->getArgOperand(1), nonExp);
	quantumRegisterSetup(&cbit);
	if(debugGenOpenQASM) errs() << "\t\tBacktrace End, Cbit Found: " << "\n";
	if(debugGenOpenQASM) cbit.printDebugMode();
	tmpDepQbit_.push_back(cbit);
	mapInstRtn_[rtnVal_] = tmpDepQbit_[0];
	tmpDepQbit_.clear();
	///// Pending...

	// qGateArg tempMeasureValue_;
	// tempMeasureValue_.isCbit = true;
	// tmpDepQbit.push_back(tempMeasureValue_);
	// backtraceOperand(CI->getArgOperand(0), 2);
	// Value * rtnVal = tmpDepQbit[0].argPtr;
	// tmpDepQbit.clear();

	// qGateArg tmpCbit_;
	// tmpCbit_.isCbit = true;
	// tmpCbit_.isPtr = true;
	// tmpDepQbit.push_back(tmpCbit_);

	// backtraceOperand(CI->getArgOperand(1), 0);
	// mapInstRtn[rtnVal] = tmpDepQbit[0];

	// tmpDepQbit.clear();

	return;
}

void GenQASM::processCallInst(CallInst * callInst){
	// bool tracked_all_operands = true;// D
	
	/* Traverse all argument operand in call inst. */
	for(unsigned iOperand = 0; iOperand < callInst->getNumArgOperands(); iOperand++){

		tmpDepQbit_.clear();
		// tmpDepQbit.clear();

		if(debugGenOpenQASM) errs() << "\tANALYZE CALL INST OPERAND NUM: " << iOperand << "\n";
		dataRepresentation argument = backtraceOperand(callInst->getArgOperand(iOperand), nonExp);
		Type* argType = callInst->getArgOperand(iOperand)->getType();

		if(isAllocQuantumType(argType)){
			quantumRegisterSetup(&argument);
			tmpDepQbit_.push_back(argument);
			if(debugGenOpenQASM) argument.printDebugMode();
		}else{
			classicalRegisterSetup(&argument);
			tmpDepQbit_.push_back(argument);
			if(debugGenOpenQASM) argument.printDebugMode();
		}
			
		allDepQbit_.push_back(tmpDepQbit_[0]);
		// 	assert(tmpDepQbit.size() == 1 && "tmpDepQbit SIZE GT 1");
		// tmpDepQbit.clear();
		tmpDepQbit_.clear();
		// }
		
	// 	qGateArg tmpQGateArg;
	// 	backtraceCount=0;

	// 	tmpQGateArg.argNum = iOperand;

	// 	//qGateArgSetup(tmpQGateArg, argType);

	// 	if(argType->isPointerTy()){
	// 		tmpQGateArg.isPtr = true;
	// 		Type *argElemType = argType->getPointerElementType();
	// 		if(argElemType->isIntegerTy(16)) tmpQGateArg.isQbit = true;
	// 		if(argElemType->isIntegerTy(1)) tmpQGateArg.isCbit = true;
	// 		if(argElemType->isIntegerTy(8)) tmpQGateArg.isAbit = true;
	// 	}else if(argType->isIntegerTy(16)){
	// 		tmpQGateArg.isQbit = true;
	// 		tmpQGateArg.valOrIndex = 0;	 
	// 	}else if(argType->isIntegerTy(32)){
	// 		if(ConstantInt *CInt = dyn_cast<ConstantInt>(callInst->getArgOperand(iOperand))){
	// 			tmpQGateArg.isParam = true;
	// 			tmpQGateArg.valOrIndex = CInt->getZExtValue();
	// 		}
	// 	}else if(argType->isIntegerTy(8)){
	// 		tmpQGateArg.isAbit = true;
	// 		tmpQGateArg.valOrIndex = 0;
	// 	}else if(argType->isIntegerTy(1)){
	// 		tmpQGateArg.isCbit = true;
	// 		tmpQGateArg.valOrIndex = 0;	 
	// 	}	  	

	// 	//check if argument is constant int	
	// 	if(ConstantInt *CInt = dyn_cast<ConstantInt>(callInst->getArgOperand(iOperand))){
	// 		tmpQGateArg.valOrIndex = CInt->getZExtValue();
	// 		if(debugGenOpenQASM)
	// 			errs() << "\tFound constant argument = " << CInt->getValue() << "\n";
	// 	}

	// 	//check if argument is constant float	
	// 	if(ConstantFP *CFP = dyn_cast<ConstantFP>(callInst->getArgOperand(iOperand))){
	// 		tmpQGateArg.val = CFP->getValueAPF().convertToDouble();
	// 		tmpQGateArg.isDouble = true;
	// 		if(debugGenOpenQASM){
	// 			errs()<<"\tCall Inst = "<<*callInst<<"\n";
	// 			errs()<<"\tFound constant double argument = "<<tmpQGateArg.val<<"\n";
	// 		}
	// 	}

	// 	tmpDepQbit.push_back(tmpQGateArg);

	// 	tracked_all_operands &= backtraceOperand(callInst->getArgOperand(iOperand),0);

	// 	if(tmpDepQbit.size()>0){
	// 		allDepQbit.push_back(tmpDepQbit[0]);
	// 		assert(tmpDepQbit.size() == 1 && "tmpDepQbit SIZE GT 1");
	// 		tmpDepQbit.clear();
	// 	}
	}
				
	//form info packet
	FnCall fnCallInfoPack;
	fnCallInfoPack.func = callInst->getCalledFunction();
	fnCallInfoPack.instPtr = callInst;
	
	// if(allDepQbit_.size() > 0){
	// 	if(debugGenOpenQASM){
	// 		errs() << "\t---Func Call Summary: " << callInst->getCalledFunction()->getName();	    
	// 		errs() << ": Has Arguments: ";       
	// 		for(unsigned int vb=0; vb<allDepQbit_.size(); vb++){
	// 			if(allDepQbit_[vb].argPtr)
	// 				errs() << allDepQbit[vb].argPtr->getName() << " ";
	// 			else
	// 				errs() << allDepQbit[vb].valOrIndex << " ";
	// 		}
	// 		errs() << "\n";
	// 	}

	// 	//populate vector of passed qubit arguments
	// 	for(unsigned int vb = 0; vb < allDepQbit.size(); vb++)
	// 		fnCallInfoPack.qArgs.push_back(allDepQbit[vb]);
	// }

	if(allDepQbit_.size() > 0){
		for(unsigned iArg = 0; iArg < allDepQbit_.size(); iArg++)
			fnCallInfoPack.qArgs_.push_back(allDepQbit_[iArg]);
	}
	fnCall.push_back(fnCallInfoPack);
	return;
}


void GenQASM::processConditionInst(BasicBlock * basicBlock, BranchInst* branchInst){
	
	if(branchInst->getNumOperands() == 3){
		if(debugGenOpenQASM) errs() << "\n\t\tBACKTRACE OPERAND CONDITION: " << "\n";
		dataRepresentation measure = backtraceOperand(branchInst->getOperand(0), cmpConstant);
		classicalRegisterSetup(&measure);
		if(debugGenOpenQASM) errs() << "\t\tBacktrace End, Value Found: " << "\n";
		if(debugGenOpenQASM) measure.printDebugMode();
		dataRepresentation cbit = backtraceOperand(branchInst->getOperand(0), nonExp);
		quantumRegisterSetup(&cbit);
		if(debugGenOpenQASM) errs() << "\t\tBacktrace End, Cbit Found: " << "\n";
		if(debugGenOpenQASM) cbit.printDebugMode();
		vector<dataRepresentation> cond({measure, cbit});
		basicBlockCondTable[basicBlock] = cond;

		if(debugGenOpenQASM)
			errs() << "\n\tIf then block: " << branchInst->getOperand(2)->getName() << "\n";
		if(debugGenOpenQASM)
			errs() << "\n\tIf end block: " << branchInst->getOperand(1)->getName() << "\n";
	}
	return;
}

void GenQASM::analyzeInst_block(BasicBlock * basicBlock, Instruction * pInst){

	unsigned numOps = pInst->getNumOperands();

	if(AllocaInst * AI = dyn_cast<AllocaInst>(pInst)){
		if(debugGenOpenQASM){
			errs() << "\n\tAllocation Instruction: " << *AI << "\n";
			errs() << "\tNum Operands: " << numOps << ";\n";
		}
	}else if(GetElementPtrInst * GEPI = dyn_cast<GetElementPtrInst>(pInst)){
		if(debugGenOpenQASM){
			errs() << "\n\tGetElementPointer Instruction: " << *GEPI << "\n";
			errs() << "\tNum Operands: " << numOps << ";\n";
		}
	}else if(CallInst * CI = dyn_cast<CallInst>(pInst)){
		if(debugGenOpenQASM){
			errs() << "\n\tCall Instruction: " << *CI << "\n";
			errs() << "\tNum Operands: " << numOps << ";\n";
		}
		if(CI->getCalledFunction()->getName() == "store_cbit"){
			processStoreCbitInst(CI);
		}else{
			processCallInst(CI);
		}
	}else if(BranchInst *BI = dyn_cast<BranchInst>(pInst)){
		if(debugGenOpenQASM){
			errs() << "\n\tBranch Instruction: " << *BI << "\n";
			errs() << "\tNum Operands: " << numOps << ";\n";
		}
		processConditionInst(basicBlock, BI);
	}
	return;
}

void GenQASM::genQASM_REG(Function* F){
	/* Print qbits declared in function. */
	for(vector<dataRepresentation>::iterator vvit = qbitsInitInCurrentFunc_.begin(),
		vvitE = qbitsInitInCurrentFunc_.end(); vvit != vvitE; ++vvit){
		
		if((*vvit).isqbit()){
			int num = accumulate((*vvit).dimSize.begin(), (*vvit).dimSize.end(), 1, multiplies<int>());
			int numDim = (*vvit).dimSize.size();
			int j = numDim-2;
			vector<int> count(numDim-1,0);
			for(int n = 0; n < num/(*vvit).dimSize[numDim-1]; n++){
				errs() << "qreg " << (*vvit).getName();
				/* dimension more than one. */
				if(j >= 0){
					for(int i = 0; i < numDim-1; i++) errs() << "_" << count[i];
					if(count[j] < (*vvit).dimSize[j]-1) count[j]++; else j--;
				}
				errs() << "[" << (*vvit).dimSize[numDim-1] << "];\n";
			}
		}

		if((*vvit).iscbit()){
			int num = accumulate((*vvit).dimSize.begin(), (*vvit).dimSize.end(), 1, multiplies<int>());
			int numDim = (*vvit).dimSize.size();
			int j = numDim-1;
			vector<int> count(numDim,0);
			for(int n = 0; n < num; n++){
				errs() << "creg " << (*vvit).getName();
				for(int i = 0; i < numDim; i++){
					errs() << "_" << count[i];
				}
				if(count[j] < (*vvit).dimSize[j]) count[j]++; else j--;
				errs() << "[1];\n";
			}
		}
	}
}

void GenQASM::genQASM_block(BasicBlock * blockBlock){
	vector<FnCall> fnCallList = fnCallTable.find(blockBlock)->second;

	for(unsigned mIndex = 0; mIndex < fnCallList.size(); mIndex++){
		/* If the FuncCall is related to quantum operation. */
		if(fnCallList[mIndex].qArgs_.size()>0){
			string fToPrint = fnCallList[mIndex].func->getName();
			if(fToPrint.find("llvm.") != string::npos) fToPrint = fToPrint.substr(5);

			//MeasX, PrepZ/X, and Fredkin require some special works, so we handle them separately
			//NB(pranav): a better way to handle these would be to decompose MeasX, PrepZ/X,
			//and Fredkin in terms of the other gates during an earlier LLVM pass

			if(fToPrint.find("MeasX") != string::npos){
				errs()<<"h " << fnCallList[mIndex].qArgs_.front().qbitVarString() << ";\n";
				fToPrint = "MeasZ";
			}

			if(fToPrint.find("MeasZ") != string::npos){
				errs()<<"measure " << fnCallList[mIndex].qArgs_.front().qbitVarString() << " -> ";

				//get inst ptr
				Value* thisInstPtr = fnCallList[mIndex].instPtr;
				map<Value*, dataRepresentation>::iterator hit = mapInstRtn_.find(thisInstPtr);
				if(hit != mapInstRtn_.end()){
					errs() << hit->second.cbitVarString() << ";\n";
				}
				continue;
			}

			if(fToPrint.find("Prep") != string::npos) {

				errs()<<"reset " << fnCallList[mIndex].qArgs_.front().qbitVarString() << ";\n";

				/////Pending...
				/* For preparation to | 1 > state, apply a bit flip after reset to get 0->1. */
				if(fnCallList[mIndex].qArgs_.back().intValue == 1)
					errs() << "x " << fnCallList[mIndex].qArgs_.front().qbitVarString() << ";\n";

				/* For preparation in X basis, change basis from Z basis with H gate. */
				if(fToPrint.find("PrepX") != string::npos)
					errs() << "h " << fnCallList[mIndex].qArgs_.front().qbitVarString() << ";\n";

				continue;
			}

			if(fToPrint.find("Fredkin") != string::npos) {
				/* Fredkin Gate Decomposition. */
				errs() << "//Decompose Fredkin(q0, q1, q2) = (I ⊗ CNOT(q1, q2)) * Toffoli(q0, q2, q1) * (I ⊗ CNOT(q1, q2))\n";
				
				//Step 1, CNOT(second input, third input)
				errs() << "cx " << fnCallList[mIndex].qArgs_[1].qbitVarString() << ", ";
				errs() << fnCallList[mIndex].qArgs_[2].qbitVarString() << ";\n";

				//Step 2, Toffoli(first input, third input, second input)
				errs() << "ccx " << fnCallList[mIndex].qArgs_[0].qbitVarString() << ", ";
				errs() << fnCallList[mIndex].qArgs_[1].qbitVarString() << ", ";
				errs() << fnCallList[mIndex].qArgs_[2].qbitVarString() << ";\n";

				//Step 3, CNOT(second input, third input)
				errs() << "cx " << fnCallList[mIndex].qArgs_[1].qbitVarString() << ", ";
				errs() << fnCallList[mIndex].qArgs_[2].qbitVarString() << ";\n";

				continue;
			}

			if(fToPrint.substr(0,2) == "Rx") fToPrint = "rx";
			else if(fToPrint.substr(0,2) == "Ry") fToPrint = "ry";
			else if(fToPrint.substr(0,2) == "Rz") fToPrint = "rz";

			if(fToPrint.find("rx") != string::npos || fToPrint.find("ry") != string::npos || fToPrint.find("rz") != string::npos){
				errs() << fToPrint << "(" << fnCallList[mIndex].qArgs_.back().val() << ") "
					<< fnCallList[mIndex].qArgs_.front().qbitVarString() << ";\n";
				continue;

			}

			if(fToPrint.find("CNOT") != string::npos) fToPrint = "cx";
			else if(fToPrint.find("Toffoli.") != string::npos) fToPrint = "ccx";
			else if(fToPrint.find("H.i") != string::npos) fToPrint = "h";
			else if(fToPrint.find("S.") != string::npos) fToPrint = "s";
			else if(fToPrint.find("T.") != string::npos) fToPrint = "t";
			else if(fToPrint.find("Sdag") != string::npos) fToPrint = "sdg";
			else if(fToPrint.find("Tdag") != string::npos) fToPrint = "tdg";
			else if(fToPrint.find("X.") != string::npos) fToPrint = "x";
			else if(fToPrint.find("Y.") != string::npos) fToPrint = "y";
			else if(fToPrint.find("Z.") != string::npos) fToPrint = "z";

			std::replace(fToPrint.begin(), fToPrint.end(), '.', '_');
			std::replace(fToPrint.begin(), fToPrint.end(), '-', '_');

			errs() << fToPrint << " ";
			for(vector<dataRepresentation>::iterator vpIt=fnCallList[mIndex].qArgs_.begin(), 
				vpItE=fnCallList[mIndex].qArgs_.end(); vpIt != vpItE-1; ++vpIt){
					errs() << vpIt->qbitVarString() << ", ";
			}
			errs()<< fnCallList[mIndex].qArgs_.back().qbitVarString() << ";\n";
    	}
    }

	/* Print conditional statement. */
	map<BasicBlock *, vector<dataRepresentation>>::iterator hit = basicBlockCondTable.find(blockBlock);
	if(basicBlockCondTable.end()!= hit){
		errs() << "if(" << hit->second.back().cbitArrayString() << " ==" << 
			hit->second.front().val() << ") ";
	}
	return ;
}

void GenQASM::getFunctionArguments(Function* F){
	for(Function::arg_iterator ait=F->arg_begin(); ait!=F->arg_end(); ++ait){

		dataRepresentation arg;
		arg.instPtr = ait;
		Type * argType = ait->getType();
		if(isAllocQuantumType(argType)){
			quantumRegisterSetup(&arg);
			qbitsInCurrentFunc_.push_back(arg);

		}else{
			classicalRegisterSetup(&arg);
		}
		funcArgList_.push_back(arg);
		if(debugGenOpenQASM) arg.printDebugMode();

		// std::string argName = (ait->getName()).str();
		// unsigned int argNum=ait->getArgNo();         

		// qGateArg tmpQArg;
		// tmpQArg.argPtr = ait;
		// tmpQArg.argNum = argNum;

		// if(argType->isPointerTy()){
		// 	if(debugGenOpenQASM) errs()<<"Argument Type: " << *argType <<"\n";
			
		// 	tmpQArg.isPtr = true;

		// 	Type *elementType = argType->getPointerElementType();
		// 	if(elementType->isIntegerTy(16)){
		// 		tmpQArg.isQbit = true;
		// 		vectQbit.push_back(ait);
		// 		qbitsInCurrentFunc.push_back(tmpQArg);
		// 		funcArgList.push_back(tmpQArg);
		// 	}else if(elementType->isIntegerTy(1)){
		// 		tmpQArg.isCbit = true;
		// 		vectQbit.push_back(ait);
		// 		qbitsInCurrentFunc.push_back(tmpQArg);
		// 		funcArgList.push_back(tmpQArg);
		// 	}else if(elementType->isIntegerTy(8)){
		// 		tmpQArg.isAbit = true;
		// 		vectQbit.push_back(ait);
		// 		qbitsInCurrentFunc.push_back(tmpQArg);
		// 		funcArgList.push_back(tmpQArg);
		// 	}else if(argType->isIntegerTy(16)){
		// 		tmpQArg.isQbit = true;
		// 		vectQbit.push_back(ait);
		// 		qbitsInCurrentFunc.push_back(tmpQArg);
		// 		funcArgList.push_back(tmpQArg);
		// 	}else if(argType->isIntegerTy(32)){
		// 		tmpQArg.isParam = true;
		// 		vectQbit.push_back(ait);
		// 		funcArgList.push_back(tmpQArg);
		// 	}else if(argType->isIntegerTy(1)){
		// 		tmpQArg.isCbit = true;
		// 		vectQbit.push_back(ait);
		// 		qbitsInCurrentFunc.push_back(tmpQArg);
		// 		funcArgList.push_back(tmpQArg);
		// 	}else if(argType->isIntegerTy(8)){
		// 		tmpQArg.isAbit = true;
		// 		vectQbit.push_back(ait);
		// 		qbitsInCurrentFunc.push_back(tmpQArg);
		// 		funcArgList.push_back(tmpQArg);
		// 	}else if(argType->isDoubleTy())
		// 		funcArgList.push_back(tmpQArg);

		// 	if(debugGenOpenQASM) print_qgateArg_debug(tmpQArg);
		// }
	}
}

/* Run - Find Datapaths for qubits. */
bool GenQASM::runOnModule(Module &M){
	vector<Function*> qFuncs;

	unsigned sccNum = 0;

	errs() << "OPENQASM 2.0;\n";
	errs() << "include \"qelib1.inc\";\n";

	/* Iterate over all functions, and over all instructions in it. */
	CallGraphNode* rootNode1 = getAnalysis<CallGraph>().getRoot();

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

				/* Initialize map structures for this function. */
				qbitsInCurrentFunc_.clear();
				qbitsInitInCurrentFunc_.clear();
				funcArgList_.clear();				

				getFunctionArguments(F);
				
				/* Iterate through all the blocks in the function. */
				for(Function::iterator BB = F->begin(), BBend = F->end(); BB != BBend; ++BB){
					BasicBlock* pBB = BB;
					
					/* Iterate through all the instructions in the block and find all the quantum alloc inst. */
					if(debugGenOpenQASM) errs() << "\n-----ANALYZE ALLOCATION INST IN BLOCK: " << pBB->getName() << "-----\n";
					for(BasicBlock::iterator instIb = pBB->begin(), instIe = pBB->end(); instIb != instIe; ++instIb){
						Instruction * pInst = &*instIb;
						if(debugGenOpenQASM)
							errs() << "\n\tProcessing Inst: " << *pInst << "\n";
						analyzeAllocInst(F,pInst);
					}
				}

				/* Process Quantum Function. */
				if(qbitsInCurrentFunc_.size()>0){
					mapQbitsInit_.insert(make_pair(F, qbitsInitInCurrentFunc_));
					mapFuncArgs_.insert(make_pair(F, funcArgList_));
					qFuncs.push_back(F);
					
					errs() << "\n-----END" << "\n";
					errs() << "\n\n-----ANALYZE QUANTUM FUNC CALL IN FUNCTION : " << F->getName() << "----\n";

					for(Function::iterator BB = F->begin(), BBend = F->end(); BB != BBend; ++BB){
						BasicBlock * basicBlock = BB;
						if(debugGenOpenQASM)
							errs() << "\nBasicBlock: " << basicBlock->getName() << "\n";

						fnCall.clear();

						for(BasicBlock::iterator instIb = basicBlock->begin(), instIe = basicBlock->end(); instIb != instIe; ++instIb){
							Instruction *pInst = &*instIb;  
							allDepQbit_.clear();

							analyzeInst_block(basicBlock, pInst);
							
						}
						fnCallTable.insert(make_pair(basicBlock, fnCall));
					}
					if(debugGenOpenQASM) errs() << "\n";
				}
			}else{
				if(debugGenOpenQASM){
					errs() << "WARNING: Ignoring external node or dummy function: ";
					if(F) errs() << F->getName();
				}
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

		for(Function::iterator BB = (*it)->begin(), BBend = (*it)->end(); BB != BBend; ++BB){
			BasicBlock * pBB = BB;
			genQASM_block(pBB);
		}
	}
	errs() << "\n";
	return false;
}
