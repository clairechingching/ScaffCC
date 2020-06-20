//===------------------- VariableTracking.cpp - Tracking variable -------------------===//
//
//                       The LLVM Scaffold Compiler Infrastructure
//
// This file was created by Scaffold Compiler Working Group
//===--------------------------------------------------------------------------------===//
// TODO: AGGRESSIVE ANALYSIS(IGNORE IF CONDITION)
#include <vector>
#include <limits>
#include <iomanip>
#include <map>
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

#define MAX_BACKTRACE_COUNT 15 //max backtrace allowed - to avoid infinite recursive loops
#define MAX_QBIT_ARR_DIM 5 //max dimensions allowed for qbit arrays

#define X_ 0
#define Y_ 1
#define Z_ 2
#define H_ 3
#define T_ 4
#define Tdag_ 5
#define S_ 6
#define Sdag_ 7
#define CNOT_ 8
#define PrepX_ 9
#define PrepZ_ 10
#define MeasX_ 11
#define MeasZ_ 12
#define Rx_ 13
#define Ry_ 14
#define Rz_ 15
#define Toffoli_ 16
#define Fredkin_ 17

bool debugVariableTracking = true;

namespace{

	enum argType{
		/* Quantum Type. */
		qbit,
		abit,
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
		vector<int> dimSize; // sized of dimensions vector

		/* Classical Inst. */
		int intValue;
		double doubValue;
		bool isClassical();
		string val();

		/* Quantum Inst. */
		bool isqbit();
		bool iscbit();
		void printQRegisterName();

		dataRepresentation() : instPtr(NULL), type(undef), isPtr(false), index(vector<int>()), dimSize(vector<int>()){}

		string getName(){ return instPtr->getName(); }
		void printDebugMode();	

	};

	bool dataRepresentation::isClassical(){
		if(type == intVal || type == doubleVal) return true; else return false;
	}

	string dataRepresentation::val(){
		stringstream ss;
		if(type == intVal) ss << " " << intValue << " ";
		if(type == doubleVal) ss << " " << doubValue << " ";
		return ss.str();		
	}

	bool dataRepresentation::isqbit(){
		if(type == qbit || type == abit) return true; else return false;
	}

	bool dataRepresentation::iscbit(){
		if(type == cbit) return true; else return false;
	}

	void dataRepresentation::printQRegisterName(){
		switch(type){
			case undef:
				errs() << " UNDEF ";
				break;
			case qbit:
			case abit:
			case cbit:
				errs() << getName();
				break;
			default:
				errs() << " error ";
				break;
		}
	}

	void dataRepresentation::printDebugMode(){
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
				case abit:
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

	argType quantumRegisterSetupHelper(dataRepresentation * qRegister, Type * type){
		if(type->isIntegerTy(16)){
			return qbit;
		}else if(type->isIntegerTy(8)){
			return abit;
		}else if(type->isIntegerTy(1)){
			return cbit;
		}else if(type->isArrayTy()){
			ArrayType * arrayType = dyn_cast<ArrayType>(type);
			qRegister->dimSize.push_back(arrayType->getNumElements());
			return quantumRegisterSetupHelper(qRegister, arrayType->getElementType());
		}else if(type->isPointerTy()){
			qRegister->isPtr = true;
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
		}else if(allocatedType->isIntegerTy(8)){
			return true;
		}else if(allocatedType->isIntegerTy(1)){
			return true;
		}else if(ArrayType * arrayType = dyn_cast<ArrayType>(allocatedType)){
			return isAllocQuantumType(arrayType->getElementType());
		}else if(PointerType  * ptrType = dyn_cast<PointerType>(allocatedType)){
			return isAllocQuantumType(ptrType->getElementType());
		}else{
			return false;
		}
	}

	struct gate_info{
		bool ptr;
		vector<int> index;
		pair<int, double> gate;
		int timestamp_;
		gate_info(){};
		gate_info(dataRepresentation * var, pair<int, double> gate_, int t):
			gate(gate_), timestamp_(t){
				if(var->isPtr){
					ptr = true;
				}else{
					ptr = false;
					index = var->index;
				}
			}
	};

	struct VariableTracking : public ModulePass {
		/* Pass Identification, Replacement for typeid. */
		static char ID;
		VariableTracking() : ModulePass(ID) {}

		// TODO: use datarepresentation here?
		// TODO: define gate represeatation?
		// TODO: gate(gate_name,index(vector<ing>), second_argument(instructions with index))
		// map<Instruction *, vector<pair<int, pair<pair<int, double>, int>>>> allocInMainFunc; // TODO:  string
		map<Instruction *, vector<gate_info>> allocInMainFunc;
		vector<dataRepresentation> qbitsInitInCurrentFunc;
		int timestamp;

		int backtraceCount;

		/* getAnalysisUsage - Requires the CallGraph. */
		virtual void getAnalysisUsage(AnalysisUsage &AU) const {
			AU.setPreservesAll();
			AU.addRequired<CallGraph>();
		}
		dataRepresentation backtraceOperand(Value * operand, backtraceExp exp);
		void backtraceOperand_helper(dataRepresentation * datRepPtr, Value * operand, int gettingIndex, backtraceExp exp);
		bool analyzeAllocInst(AllocaInst * inst);
		bool analyzeCallInst(CallInst * inst);
		bool analyzeStoreCbitInst(CallInst * inst);
		/* Run - Print out SCCs in the call graph for the module. */
		bool runOnModule(Module &M);
	};
}

char VariableTracking::ID = 0;
static RegisterPass<VariableTracking>
X("var-tracking", "Quantum Variables Tracking..."); //spatil: should be Z or X??

void VariableTracking::backtraceOperand_helper(dataRepresentation * datRepPtr, Value * operand, int gettingIndex, backtraceExp exp){

	if(backtraceCount > MAX_BACKTRACE_COUNT){
		errs() << "Exceed max backtrace count...";
		return;
	}else{
		backtraceCount++;
	}

	if(AllocaInst * AI = dyn_cast<AllocaInst>(operand)){
		if(debugVariableTracking)
			errs() << "\n\t\tAlloca inst Found: " << *AI << "\n";
		datRepPtr->instPtr = AI;
		if(datRepPtr->isPtr){
			// TODO: FORGET THE LOGIC if(debugVariableTracking) errs() << "pointer here";
			for(vector<dataRepresentation>::iterator vvit = qbitsInitInCurrentFunc.begin(),
				vvitE = qbitsInitInCurrentFunc.end(); vvit != vvitE; ++vvit){
				if((*vvit).iscbit()){
					(*vvit).isPtr = true;
				}
			}	
		}
		return;

	}else if(GetElementPtrInst * GEPI = dyn_cast<GetElementPtrInst>(operand)){
		if(debugVariableTracking)
			errs() << "\n\t\tGetElemPtr inst Found: " << *GEPI << "\n";
		/* Get index. */
		if(GEPI->getNumOperands() == 3){
			if(exp == ptrToArray){
				ConstantInt * CInt = dyn_cast<ConstantInt>(GEPI->getOperand(2));
				int index = CInt->getSExtValue();
				if(debugVariableTracking) errs() << "\t\t[" << gettingIndex << "] Index: " << index << "\n";
				backtraceOperand_helper(datRepPtr, GEPI->getOperand(0), gettingIndex, exp);
			}else if(GEPI->getOperand(2)->getType()->isIntegerTy(32)){
				/* Merely a pointer. */
				datRepPtr->isPtr = true;
				backtraceOperand_helper(datRepPtr, GEPI->getOperand(0), gettingIndex, exp);
			}else{
				ConstantInt * CInt = dyn_cast<ConstantInt>(GEPI->getOperand(2));
				int index = CInt->getSExtValue();
				if(debugVariableTracking) errs() << "\t\t[" << gettingIndex << "] Index: " << index << "\n";
				datRepPtr->index.push_back(index);
				backtraceOperand_helper(datRepPtr, GEPI->getOperand(0), gettingIndex, exp);
			}
		}else if(GEPI->getNumOperands() == 2){
			ConstantInt * CInt = dyn_cast<ConstantInt>(GEPI->getOperand(1));
			int index = CInt->getSExtValue();
			if(debugVariableTracking) errs() << "\t\t[" << gettingIndex << "] Index: " << index << "\n";
			datRepPtr->index.push_back(index);
			backtraceOperand_helper(datRepPtr, GEPI->getOperand(0), gettingIndex, ptrToArray);
      errs().flush();
		}else{
			errs() << "UNHANDLED GEPI CASE, BOOOOOOOOOO!\n";
		}
		return;

	}else if(CallInst * CI = dyn_cast<CallInst>(operand)){
		if(debugVariableTracking)
			errs() << "\n\t\tCall inst Found: " << *CI << "\n";
		if(CI->getCalledFunction()->getName().find("llvm.Meas") != string::npos){
			if(debugVariableTracking){
         errs() << "\n\t\tBACKTRACE OPERAND QUBIT: \n";
			   errs().flush();
      }
      backtraceOperand_helper(datRepPtr, CI->getOperand(0), gettingIndex, exp);
		}
		return;
	}else if(PtrToIntInst * PTTI = dyn_cast<PtrToIntInst>(operand)){
		if(debugVariableTracking)
			errs() << "\n\t\tPtrToInt inst Found: " << *PTTI << "\n";
		backtraceOperand_helper(datRepPtr, PTTI->getOperand(0), 0, exp);
		return;
	}else if(ConstantInt * CInt = dyn_cast<ConstantInt>(operand)){
		datRepPtr->instPtr = CInt;
		if(debugVariableTracking) errs() << "\n\t\tInt Constant Found: " << CInt->getSExtValue() << "\n";
		return;
	}else if(ConstantFP * CFP = dyn_cast<ConstantFP>(operand)){
		datRepPtr->instPtr = CFP;
		if(debugVariableTracking) errs() << "\n\t\tDouble Constant Found: " << CFP->getValueAPF().convertToDouble() << "\n";
		return;
	}else if(LoadInst * LI = dyn_cast<LoadInst>(operand)){
		if(debugVariableTracking) errs() << "\n\t\tLoad inst Found: " << *LI << "\n";
		if(exp == cmpConstant){
			if(debugVariableTracking) errs() << "\n\t\tCmp constant is 1.\n";
			datRepPtr->type = intVal;
			datRepPtr->intValue = 1;
			return;
		}else{
			backtraceOperand_helper(datRepPtr, LI->getOperand(0), 0, exp);
			return;
		}
	}else if(CmpInst * CMPI = dyn_cast<CmpInst>(operand)){
		if(debugVariableTracking) errs() << "\n\t\tCompare inst Found: " << *CMPI << "\n";
		if(exp == cmpConstant){
			backtraceOperand_helper(datRepPtr, CMPI->getOperand(1), 0, exp);
		}else{
			backtraceOperand_helper(datRepPtr, CMPI->getOperand(0), 0, exp);
		}
		return;
	}else if(ZExtInst * ZEI = dyn_cast<ZExtInst>(operand)){
		if(debugVariableTracking) errs() << "\n\t\tZExt inst Found: " << *ZEI << "\n";
		backtraceOperand_helper(datRepPtr, ZEI->getOperand(0), 0, exp);
		return;
	}else if(isa<UndefValue>(operand)){
		datRepPtr->type = undef;
		if(debugVariableTracking) errs() << "Undef Inst: " << *operand << "\n";
		return;
	}else{
		if(debugVariableTracking) errs() << "UNHANDLED CASE, BOOOOOOOOOO! Inst: " << *operand << "\n";
		return;
	}
}

dataRepresentation VariableTracking::backtraceOperand(Value * operand, backtraceExp exp){

	backtraceCount = 0;

	dataRepresentation returnDR;
	int gettingIndex = 0;

	backtraceOperand_helper(&returnDR, operand, gettingIndex, exp);
	
	return returnDR;
}

bool VariableTracking::analyzeAllocInst(AllocaInst * AI){
	
	if(debugVariableTracking){
		errs() << "\n\tAllocation Instruction: " << *AI << "\n";		
	}
	Type * allocatedType_ = AI->getAllocatedType();

		if(isAllocQuantumType(allocatedType_)){

			if(debugVariableTracking) errs() << "\tNew qubit allocation: " << AI->getName() << "\n";

			dataRepresentation qRegister;
			qRegister.instPtr = AI;
			quantumRegisterSetup(&qRegister);
			
			if(debugVariableTracking) qRegister.printDebugMode();

			if(qRegister.instPtr->getName().find(".addr")!= string::npos){
			
				/* Note: Necessary if -mem2reg is not run on IR before.
					Eg, without -mem2reg
						module(i8 * %q){
							%q.addr = alloca i8*, align 8
							...
						}
						qbit q.addr must be mapped to argement q. */

				if(qRegister.type == qbit || qRegister.type == abit){
					// TODO: CLEAN UP
					// bool qbitExisting = false;
					// string qbitname = qRegister.instPtr->getName().str();
					// unsigned pos = qbitname.find(".addr");
					// qbitname = qbitname.substr(0, pos);
					// for(vector<dataRepresentation>::iterator vvit = funcArgList.begin(),
					// 	vvitE = funcArgList.end(); ((vvit != vvitE) && !qbitExisting); ++vvit){
					// 	if((*vvit).instPtr->getName() == qbitname) qbitExisting = true;
					// }
				}else{
					//qubits/new qubits in function
					vector<gate_info> gate;
					allocInMainFunc[AI] = gate;
					qbitsInitInCurrentFunc.push_back(qRegister);
				}
			}else{
				//qubits/new qubits in function
				vector<gate_info> gate;
				allocInMainFunc[AI] = gate;				
				qbitsInitInCurrentFunc.push_back(qRegister);
			}
		}

	return true;
}

bool VariableTracking::analyzeCallInst(CallInst * inst){

	vector<gate_info> * gates;
	//TODO: ASSERT THE NUMBER OF OPERANDS
	int nOperand = inst->getNumArgOperands();
	
	if(debugVariableTracking){
		errs() << "\n\tCall Instruction: " << *inst << "\n";
		errs() << "The number of operands: " << nOperand << "\n";
	}

	Function *callee = inst->getCalledFunction();
	if(callee->isIntrinsic()){

		int gate_num = -1;

		if(callee->getName().find("llvm.MeasX.") != std::string::npos){
			if(debugVariableTracking) errs() << "\tFind MeasX Gate.\n";
			gate_num = MeasX_;
		}else if(callee->getName().find("llvm.MeasZ.") != std::string::npos){
			if(debugVariableTracking) errs() << "\tFind MeasZ Gate.\n";
			gate_num = MeasZ_;	
		}else if(callee->getName().find("llvm.H.") != std::string::npos){
			if(debugVariableTracking) errs() << "\tFind H Gate.\n";
			gate_num = H_;
		}else if(callee->getName().find("llvm.Tdag.") != std::string::npos){
			if(debugVariableTracking) errs() << "\tFind Tdag Gate.\n";
			gate_num = Tdag_;
		}else if(callee->getName().find("llvm.T.") != std::string::npos){
			if(debugVariableTracking) errs() << "\tFind T Gate.\n";
			gate_num = T_;
		}else if(callee->getName().find("llvm.Sdag.") != std::string::npos){
			if(debugVariableTracking) errs() << "\tFind Sdag Gate.\n";
			gate_num = Sdag_;
		}else if(callee->getName().find("llvm.S.") != std::string::npos){
			if(debugVariableTracking) errs() << "\tFind S Gate.\n";
			gate_num = S_;
		}else if(callee->getName().find("llvm.X.") != std::string::npos){
			if(debugVariableTracking) errs() << "\tFind X Gate.\n";
			gate_num = X_;
		}else if(callee->getName().find("llvm.Y.") != std::string::npos){
			if(debugVariableTracking) errs() << "\tFind Y Gate.\n";
			gate_num = Y_;	
		}else if(callee->getName().find("llvm.Z.") != std::string::npos){
			if(debugVariableTracking) errs() << "\tFind Z Gate.\n";
			gate_num = Z_;	
		}else if(callee->getName().find("llvm.CNOT.") != std::string::npos){
			if(debugVariableTracking) errs() << "\tFind CNOT Gate.\n";
			gate_num = CNOT_;	
		}else if(callee->getName().find("llvm.PrepX.") != std::string::npos){
			if(debugVariableTracking) errs() << "\tFind PrepX Gate.\n";
			gate_num = PrepX_;	
		}else if(callee->getName().find("llvm.PrepZ.") != std::string::npos){
			if(debugVariableTracking) errs() << "\tFind PrepZ Gate.\n";
			gate_num = PrepZ_;	
		}else if(callee->getName().find("llvm.Rx.") != std::string::npos){
			if(debugVariableTracking) errs() << "\tFind Rx Gate.\n";
			gate_num = Rx_;	
		}else if(callee->getName().find("llvm.Ry.") != std::string::npos){
			if(debugVariableTracking) errs() << "\tFind Ry Gate.\n";
			gate_num = Ry_;	
		}else if(callee->getName().find("llvm.Rz.") != std::string::npos){
			if(debugVariableTracking) errs() << "\tFind Rz Gate.\n";
			gate_num = Rz_;	
		}else if(callee->getName().find("llvm.Toffoli.") != std::string::npos){
			if(debugVariableTracking) errs() << "\tFind Toffoli Gate.\n";
			gate_num = Toffoli_;	
		}else if(callee->getName().find("llvm.Fredkin.") != std::string::npos){
			if(debugVariableTracking) errs() << "\tFind Fredkin Gate.\n";
			gate_num = Fredkin_;
		}else if(inst->getCalledFunction()->getName().find("afree") != std::string::npos){
			if(debugVariableTracking) errs() << "\tBegin free...\n";
			if(debugVariableTracking) errs() << "\tName: " << inst->getArgOperand(0)->getName() << "\n";
			// uint64_t addNum = 0;
			// if (llvm::ConstantInt* consInt = dyn_cast<llvm::ConstantInt>(CI->getArgOperand(1))){
			// 	addNum = consInt -> getLimitedValue();
			// 	errs() << "This Is The Value: " << addNum;
			// }else{
			// 	addNum = 1;
			// }
			// FunctionResources[F][Net_A_] -= addNum;
			// errs() << "Net Then Width" << FunctionResources[F][Net_A_] << " " << FunctionResources[F][Width_] << "\n"; 
			if(debugVariableTracking) errs() << "Finish free.\n";
		}

		switch(gate_num){
			case MeasX_:
			case MeasZ_:
			case H_:
			case Tdag_:
			case T_:
			case Sdag_:
			case S_:
			case X_:
			case Y_:
			case Z_:{

				dataRepresentation argument = backtraceOperand(inst->getArgOperand(0), nonExp);
				// TODO: ASSERT QUANTUM TYPE
				quantumRegisterSetup(&argument);
				if(Instruction * allocInst = dyn_cast<Instruction>(argument.instPtr)){
					gates = &(allocInMainFunc[allocInst]);
					if(debugVariableTracking) argument.printDebugMode();
					pair<int, double> gate_(gate_num, 0.0);
					gate_info gate(&argument, gate_, timestamp);
					gates->push_back(gate);
				}
				break;
			}
			case PrepX_:
			case PrepZ_:{
				dataRepresentation argument = backtraceOperand(inst->getArgOperand(0), nonExp);
				// TODO: ASSERT QUANTUM TYPE
				quantumRegisterSetup(&argument);

				dataRepresentation constant = backtraceOperand(inst->getArgOperand(1), nonExp);
				classicalRegisterSetup(&constant);

				if(Instruction * allocInst = dyn_cast<Instruction>(argument.instPtr)){
					gates = &(allocInMainFunc[allocInst]);
					if(debugVariableTracking) argument.printDebugMode();
					pair<int, double> gate_(gate_num, constant.intValue * 1.0);
					gate_info gate(&argument, gate_, timestamp);
					gates->push_back(gate);
				}
				break;
			}
			case Rx_:
			case Ry_:
			case Rz_:{
				dataRepresentation argument = backtraceOperand(inst->getArgOperand(0), nonExp);
				// TODO: ASSERT QUANTUM TYPE
				quantumRegisterSetup(&argument);

				dataRepresentation constant = backtraceOperand(inst->getArgOperand(1), nonExp);
				classicalRegisterSetup(&constant);

				if(Instruction * allocInst = dyn_cast<Instruction>(argument.instPtr)){
					gates = &(allocInMainFunc[allocInst]);
					if(debugVariableTracking) argument.printDebugMode();
					pair<int, double> gate_(gate_num, constant.doubValue);
					gate_info gate(&argument, gate_, timestamp);
					gates->push_back(gate);
				}

				break;
			}
			case CNOT_:{
				// TODO: CHECK WHICH ONE IS CONTROL AND WHICH ONE IS TARGET
				dataRepresentation target = backtraceOperand(inst->getArgOperand(0), nonExp);
				// TODO: ASSERT QUANTUM TYPE
				quantumRegisterSetup(&target);
				if(Instruction * allocInst = dyn_cast<Instruction>(target.instPtr)){
					gates = &(allocInMainFunc[allocInst]);
					if(debugVariableTracking) target.printDebugMode();
					pair<int, double> gate_(gate_num, 0.0);
					gate_info gate(&target, gate_, timestamp);
					gates->push_back(gate);
				}

				dataRepresentation control = backtraceOperand(inst->getArgOperand(1), nonExp);
				// TODO: ASSERT QUANTUM TYPE
				quantumRegisterSetup(&control);
				//TODO: CHANGE TO ASSERT
				if(Instruction * allocInst = dyn_cast<Instruction>(control.instPtr)){
					gates = &(allocInMainFunc[allocInst]);
					if(debugVariableTracking) control.printDebugMode();
					pair<int, double> gate_(gate_num, 1.0);
					gate_info gate(&control, gate_, timestamp);
					gates->push_back(gate);
				}
				break;
			}
			case Toffoli_:
			case Fredkin_:{
				// TODO: THREE arguments
				// TODO: CHECK WHICH ONE IS CONTROL AND WHICH ONE IS TARGET
				dataRepresentation target = backtraceOperand(inst->getArgOperand(0), nonExp);
				// TODO: ASSERT QUANTUM TYPE
				quantumRegisterSetup(&target);
				if(Instruction * allocInst = dyn_cast<Instruction>(target.instPtr)){
					gates = &(allocInMainFunc[allocInst]);
					if(debugVariableTracking) target.printDebugMode();
					pair<int, double> gate_(gate_num, 0.0);
					gate_info gate(&target, gate_, timestamp);
					gates->push_back(gate);
				}
				
				dataRepresentation control = backtraceOperand(inst->getArgOperand(1), nonExp);
				// TODO: ASSERT QUANTUM TYPE
				quantumRegisterSetup(&control);
				//TODO: CHANGE TO ASSERT
				if(Instruction * allocInst = dyn_cast<Instruction>(control.instPtr)){
					gates = &(allocInMainFunc[allocInst]);
					if(debugVariableTracking) control.printDebugMode();
					pair<int, double> gate_(gate_num, 1.0);
					gate_info gate(&control, gate_, timestamp);
					gates->push_back(gate);
				}


				dataRepresentation control_ = backtraceOperand(inst->getArgOperand(2), nonExp);
				// TODO: ASSERT QUANTUM TYPE
				quantumRegisterSetup(&control_);
				//TODO: CHANGE TO ASSERT
				if(Instruction * allocInst = dyn_cast<Instruction>(control_.instPtr)){
					gates = &(allocInMainFunc[allocInst]);
					if(debugVariableTracking) control_.printDebugMode();
					pair<int, double> gate_(gate_num, 2.0);
					gate_info gate(&control_, gate_, timestamp);
					gates->push_back(gate);	
				}			
				break;
			}
			default:
				break;	
		}
	}else{
		/* Non-intrinsic Function Call, resource has been entered for this call previously.
			Look them up and add to the resource table in this function. */
		// if (FunctionResources.find(callee) != FunctionResources.end()){
		// unsigned long long* callee_numbers = FunctionResources.find(callee)->second;
		// FunctionResources[F][14] += callee_numbers[14];
		// if(callee_numbers[3] > FunctionResources[F][3] - FunctionResources[F][2])
		// FunctionResources[F][3] = FunctionResources[F][2] + callee_numbers[3];
		// for (int l=0; l<NCOUNTS; l++) if(l!=3) FunctionResources[F][l] += callee_numbers[l];
		// }
	}	

	// TODO: BACK TRACK TO WHEN IT'S ALLOCATED
	// TODO: PUSH THE GATE TO VECTOR
	// TODO: TIMESTEP? (LINKED_LIST?)
	// vector<int> * gate;
	// for(unsigned iOperand  = 0; iOperand < inst->getNumArgOperands(); iOperand++){
	// 	if(debugVariableTracking) errs() << "\tANALYZE CALL INST OPERAND NUM: " << iOperand << "\n";
	// 	dataRepresentation argument = backtraceOperand(inst->getArgOperand(iOperand), nonExp);
	// 	Type* argType = inst->getArgOperand(iOperand)->getType();

	// 	if(isAllocQuantumType(argType)){
	// 		quantumRegisterSetup(&argument);
	// 		if(Instruction * allocInst = dyn_cast<Instruction>(argument.instPtr)){
	// 			gate = &(allocInMainFunc[allocInst]);
	// 		}
	// 		if(debugVariableTracking) argument.printDebugMode();
	// 	}else{
	// 		classicalRegisterSetup(&argument);
	// 		if(debugVariableTracking) argument.printDebugMode();
	// 	}		
	// }

	timestamp++;
	return true;
}

// TODO: 
bool VariableTracking::analyzeStoreCbitInst(CallInst * CI){
	// TODO: ASSERT NEXT OPERAND IS MEASUREMENT 
	// Value * rtnVal_ = CI->getArgOperand(0);

	vector<gate_info> * gates;

	if(debugVariableTracking) errs() << "\n\t\tBACKTRACE OPERAND CBIT: \n";
	dataRepresentation cbit = backtraceOperand(CI->getArgOperand(1), nonExp);
	quantumRegisterSetup(&cbit);
	if(debugVariableTracking) errs() << "\t\tBacktrace End, Cbit Found: " << "\n";
	if(debugVariableTracking) cbit.printDebugMode();

	//TODO: CHANGE TO ASSERT
	if(Instruction * allocInst = dyn_cast<Instruction>(cbit.instPtr)){
		int gate_num;
		gates = &(allocInMainFunc[allocInst]);
		if(debugVariableTracking) cbit.printDebugMode();
		// TODO: MEASX OR MEASZ
		if(CallInst * CI_ = dyn_cast<CallInst>(CI->getArgOperand(0))){
			Function * callee = CI_->getCalledFunction();
			if(callee->isIntrinsic()){
				if(callee->getName().find("llvm.MeasZ.") != std::string::npos){
					if(debugVariableTracking) errs() << "\tFind MeasX Gate.\n";
					gate_num = MeasZ_;
				}else if(callee->getName().find("llvm.MeasX.") != std::string::npos){
					if(debugVariableTracking) errs() << "\tFind MeasX Gate.\n";
					gate_num = MeasX_;
				}
			}
		}
		pair<int, double> gate_(gate_num, 0.0);
		gate_info gate(&cbit, gate_, timestamp);
		gates->push_back(gate);	
	}

	return true;
}

/* Run - Find Datapaths for qubits. */
bool VariableTracking::runOnModule(Module &M){
    errs() << "Quantum Variables and Theirs Path, ";

	// There should be only main function after flatten.
	CallGraphNode* rootNode = getAnalysis<CallGraph>().getRoot();
	unsigned sccNum = 0;

	// TODO: what is SCC(Strongly Connected Component)?
	for(scc_iterator<CallGraphNode*> sccIb = scc_begin(rootNode),
		E = scc_end(rootNode); sccIb != E; ++sccIb ){
		if(debugVariableTracking)
			errs() << "\nSCC #" << ++sccNum << "\n";
		const std::vector<CallGraphNode *> &nextSCC = * sccIb;
		for(std::vector<CallGraphNode *>::const_iterator nsccI = nextSCC.begin(),
			E = nextSCC.end(); nsccI != E; ++nsccI){
			Function * F = (*nsccI)->getFunction();
			if(F && !F->isDeclaration()){
				if(debugVariableTracking)
					errs() << "Processing Function: " << F->getName() << "\n";
				for(Function::iterator BB = F->begin(), BBend = F->end(); BB != BBend; ++BB){
					BasicBlock * pBB = BB;
					for(BasicBlock::iterator instIb = pBB->begin(), instIe = pBB->end(); instIb != instIe; ++instIb){
						Instruction * pInst = &*instIb;
						if(debugVariableTracking)
							errs() << "\n\tProcessing Inst: " << *pInst << "\n";
						if(AllocaInst * AI = dyn_cast<AllocaInst>(pInst)){
							analyzeAllocInst(AI);
						}else if(CallInst * CI = dyn_cast<CallInst>(pInst)){
							if(CI->getCalledFunction()->getName() == "store_cbit") analyzeStoreCbitInst(CI);
							else analyzeCallInst(CI);
						}	
					}
				}
			}
		} 
	}

	// print the timestep
	for(auto i = 0; i < timestamp + 1; i++) errs() <<'\t' << '\t' << i;
	errs() << '\n';

	for(auto it = allocInMainFunc.begin(); it != allocInMainFunc.end(); it++){
		// TODO: PRINT WITH TIMESTAMP
		errs() << it->first->getName() << '\t' << '\t';

		int curr = 0;

		for(auto it_ = it->second.begin(); it_ != it->second.end(); it_++){
			for(auto j = curr; j < it_->timestamp_; j++){
				errs() << '\t' << '\t';
				curr++;
			}
			// errs() << it_->first.first << ' ' << it_->first.second;

			switch(it_->gate.first){
				case MeasX_:{
					errs() << "MeasX";
					break;
				}
				case MeasZ_:{
					errs() << "MeasZ";
					break;
				}
				case H_:{
					errs() << "H";
					break;
				}
				case Tdag_:{
					errs() << "Tdag";
					break;
				}
				case T_:{
					errs() << "T";
					break;
				}
				case Sdag_:{
					errs() << "Sdag";
					break;
				}
				case S_:{
					errs() << "S";
					break;
				}
				case X_:{
					errs() << "X";
					break;
				}
				case Y_:{
					errs() << "Y";
					break;
				}
				case Z_:{
					errs() << "Z";
					break;
				}
				// TODO: CAST TO INT
				case PrepX_:
					errs() << "PrepX, ";
					errs() << (int)it_->gate.second;
					break;
				case PrepZ_:{
					errs() << "PrepZ, ";
					errs() << (int)it_->gate.second;
					break;
				}
				case Rx_:{
					errs() << "Rx";
					errs() << it_->gate.second;
					break;
				}
				case Ry_:{
					errs() << "Ry";
					errs() << it_->gate.second;
					break;
				}
				case Rz_:{
					errs() << "Rz";
					errs() << it_->gate.second;
					break;
				}
				case CNOT_:{
					errs() << "CNOT";
					switch((int)it_->gate.second){
						case 0:
							errs() << "(c)";
							break;
						case 1:
							errs() << "(t)";
							break;
					}
					break;
				}
				case Toffoli_:{
					errs() << "Toffoli";
					switch((int)it_->gate.second){
						case 0:
							errs() << "(c)";
							break;
						case 1:
							errs() << "(t)";
							break;
						case 2:
							errs() << "(t)";
							break;
					}
					break;
				}
				case Fredkin_:{
					errs() << "Fredkin";
					switch((int)it_->gate.second){
						case 0:
							errs() << "(c)";
							break;
						case 1:
							errs() << "(t)";
							break;
						case 2:
							errs() << "(t)";
							break;
					}
					break;
				}
				default:
					break;	
			}
			if(!(it_->ptr)){
				for(auto i = it_->index.begin(); i != it_->index.end(); i++){
					errs() << '[' << *i << ']';
				}
			}
			
		}
		errs() << '\n';
	}
	
	return false;
}