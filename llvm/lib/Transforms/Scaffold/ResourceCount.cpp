//===----------------------------- ResourceCount2.cpp -------------------------===//
// This file implements the Scaffold Pass of counting the number of qbits and
// gates in a program in callgraph post-order. Printing total for every function.
//
//        This file was created by Scaffold Compiler Working Group
//
//===--------------------------------------------------------------------------===//

#define DEBUG_TYPE "ResourceCount2"
#include <vector>
#include <limits>
#include <map>
#include "llvm/Pass.h"
#include "llvm/Function.h"
#include "llvm/Module.h"
#include "llvm/BasicBlock.h"
#include "llvm/Instruction.h"
#include "llvm/Instructions.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/PassAnalysisSupport.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Support/CFG.h"
#include "llvm/ADT/SCCIterator.h"

#include "llvm/Constants.h"

#define NCOUNTS 22

#define Qbits_ 0
#define Gross_A_ 1
#define Net_A_ 2
#define Width_ 3
#define X_ 4
#define Y_ 5
#define Z_ 6
#define H_ 7
#define T_ 8
#define Tdag_ 9
#define S_ 10
#define Sdag_ 11
#define CNOT_ 12
#define PrepX_ 13
#define PrepZ_ 14
#define MeasX_ 15
#define MeasZ_ 16
#define Rx_ 17
#define Ry_ 18
#define Rz_ 19
#define Toffoli_ 20
#define Fredkin_ 21
#define All_ 22

using namespace llvm;

bool debugResourceCount = true;

// An anonymous namespace for the pass. Things declared inside it are
// only visible to the current file.
namespace {
  unsigned long long app_total_gates;

  enum argType{
    /* Quantum Type. */
    qbit,
    abit,
    cbit, 

    undef
  };

  struct quantumRepresentation{
    Value * instPtr;
    argType type;
    bool isPtr;
    std::vector<int> index;
    std::vector<int> dimSize;

    quantumRepresentation() : instPtr(NULL), type(undef), isPtr(false), index({}), dimSize({}){}

    void printDebugMode();
    std::string getName();
    int count();

  };

  int quantumRepresentation::count(){
    int sum = 0;
    for(std::vector<int>::iterator it = dimSize.begin(); it != dimSize.end(); ++it)
      sum += *it;
    return sum;
  }

  std::string quantumRepresentation::getName(){
    return instPtr->getName();
  }

  void quantumRepresentation::printDebugMode(){
    errs() << "\t\tPrinting Quantum Register:\n";
    errs() << "\t\tName: " << getName();
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

  argType quantumRegisterSetupHelper(quantumRepresentation * qRegister, Type * type){
		if(type->isIntegerTy(16)){
			return qbit;
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

  void quantumRegisterSetup(quantumRepresentation * qRegister){
		AllocaInst * AI = dyn_cast<AllocaInst>(qRegister->instPtr);
		Type * allocatedType = AI->getAllocatedType();
		qRegister->type = quantumRegisterSetupHelper(qRegister, allocatedType);
  }

  bool isAllocQuantumType(Type * allocatedType){
  if(allocatedType->isIntegerTy(16)){
    return true;
  }else if(ArrayType * arrayType = dyn_cast<ArrayType>(allocatedType)){
    return isAllocQuantumType(arrayType->getElementType());
  }else{
    return false;
  }
}

  /* ResourceCount Pass to count qbits in functions. */
  struct ResourceCount : public ModulePass {

    /* Pass Identification. */
    static char ID;
    ResourceCount() : ModulePass(ID) {}

		/* getAnalysisUsage - Requires the CallGraph. */
    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
      AU.setPreservesAll();  
      AU.addRequired<CallGraph>();    
    }
    
    void CountFunctionResources (Function *F, std::map <Function*, unsigned long long* > &FunctionResources) const {
      /* Traverse instruction by instruction. */
      for (inst_iterator I = inst_begin(*F), E = inst_end(*F); I != E; ++I) {
        /* Grab pointer to instruction reference. */
        Instruction *Inst = &*I;

        if(AllocaInst * AI = dyn_cast<AllocaInst>(Inst)){
          if(debugResourceCount) errs() << "\n\tAllocation Instruction: " << *AI << "\n";
          Type * allocatedType_ = AI->getAllocatedType();
           if(isAllocQuantumType(allocatedType_)){
            if(debugResourceCount) errs() << "\tNew qubit allocation: " << AI->getName() << "\n";
            quantumRepresentation qRegister;
            qRegister.instPtr = AI;
            quantumRegisterSetup(&qRegister);
            if(debugResourceCount) qRegister.printDebugMode();
            int n = qRegister.count();
            FunctionResources[F][Qbits_] += n;
          }
        }else if(GetElementPtrInst * GEPI = dyn_cast<GetElementPtrInst>(Inst)){
          if(debugResourceCount) errs() << "\n\tGetElementPointer Instruction: " << *GEPI << "\n";
        }else if(CallInst * CI = dyn_cast<CallInst>(Inst)){
          if(debugResourceCount) errs() << "\n\tCall Instruction: " << *CI << "\n";
        }else if(BranchInst * BI = dyn_cast<BranchInst>(Inst)){
          if(debugResourceCount) errs() << "\n\tBranch Instruction: " << *BI << "\n";
        }else if(LoadInst * LI = dyn_cast<LoadInst>(Inst)){
          if(debugResourceCount) errs() << "\n\tLoad Instruction: " << *LI << "\n";
        }else if(StoreInst * SI = dyn_cast<StoreInst>(Inst)){
          if(debugResourceCount) errs() << "\n\tStore Instruction: " << *SI << "\n";
        }else{
          if(debugResourceCount) errs() << "\n\tUnhandled Instruction: " << *Inst << "\n";
        }
  
        if(CallInst * CI = dyn_cast<CallInst>(Inst)){
          if(debugResourceCount) errs() << "\tCall Inst: " << *CI << "\n";
          Function *callee = CI->getCalledFunction();
          //if(callee->isIntrinsic()){
            
            if(callee->getName().find("llvm.MeasX.") != std::string::npos){
              if(debugResourceCount) errs() << "\tFind MeasX Gate.\n";
              FunctionResources[F][All_]++;
              FunctionResources[F][MeasX_]++;
            }else if(callee->getName().find("llvm.MeasZ.") != std::string::npos){
              if(debugResourceCount) errs() << "\tFind MeasZ Gate.\n";
              FunctionResources[F][All_]++;
              FunctionResources[F][MeasZ_]++;
            }else if(callee->getName().find("llvm.H.") != std::string::npos){
              if(debugResourceCount) errs() << "\tFind H Gate.\n";
              FunctionResources[F][All_]++;
              FunctionResources[F][H_]++;
            }else if(callee->getName().find("llvm.Tdag.") != std::string::npos){
              if(debugResourceCount) errs() << "\tFind Tdag Gate.\n";
              FunctionResources[F][All_]++;
              FunctionResources[F][Tdag_]++;
            }else if(callee->getName().find("llvm.T.") != std::string::npos){
              if(debugResourceCount) errs() << "\tFind T Gate.\n";
              FunctionResources[F][All_]++;              
              FunctionResources[F][T_]++;
            }else if(callee->getName().find("llvm.Sdag.") != std::string::npos){
              if(debugResourceCount) errs() << "\tFind Sdag Gate.\n";
              FunctionResources[F][All_]++;
              FunctionResources[F][Sdag_]++;
            }else if(callee->getName().find("llvm.S.") != std::string::npos){
              if(debugResourceCount) errs() << "\tFind S Gate.\n";
              FunctionResources[F][All_]++;
              FunctionResources[F][S_]++;
            }else if(callee->getName().find("llvm.CNOT.") != std::string::npos){
              if(debugResourceCount) errs() << "\tFind CNOT Gate.\n";
              FunctionResources[F][All_]++;
              FunctionResources[F][CNOT_]++;
            }else if(callee->getName().find("llvm.PrepX.") != std::string::npos){
              if(debugResourceCount) errs() << "\tFind PrepX Gate.\n";
              FunctionResources[F][All_]++;
              FunctionResources[F][PrepX_]++;
            }else if(callee->getName().find("llvm.PrepZ.") != std::string::npos){
              if(debugResourceCount) errs() << "\tFind PrepZ Gate.\n";
              FunctionResources[F][All_]++;
              FunctionResources[F][PrepZ_]++;
            }else if(callee->getName().find("llvm.X.") != std::string::npos){
              if(debugResourceCount) errs() << "\tFind X Gate.\n";
              FunctionResources[F][All_]++;
              FunctionResources[F][X_]++;
            }else if(callee->getName().find("llvm.Y.") != std::string::npos){
              if(debugResourceCount) errs() << "\tFind Y Gate.\n";
              FunctionResources[F][All_]++;
              FunctionResources[F][Y_]++;
            }else if(callee->getName().find("llvm.Z.") != std::string::npos){
              if(debugResourceCount) errs() << "\tFind Z Gate.\n";
              FunctionResources[F][All_]++;
              FunctionResources[F][Z_]++;              
            }else if(callee->getName().find("llvm.Rx.") != std::string::npos){
              if(debugResourceCount) errs() << "\tFind Rx Gate.\n";
              FunctionResources[F][All_]++;
              FunctionResources[F][Rx_]++;              
            }else if(callee->getName().find("llvm.Ry.") != std::string::npos){
              if(debugResourceCount) errs() << "\tFind Ry Gate.\n";
              FunctionResources[F][All_]++;
              FunctionResources[F][Ry_]++;
            }else if(callee->getName().find("llvm.Rz.") != std::string::npos){
              if(debugResourceCount) errs() << "\tFind Rz Gate.\n";
              FunctionResources[F][All_]++;
              FunctionResources[F][Rz_]++;
            }else if(callee->getName().find("llvm.Toffoli.") != std::string::npos){
              if(debugResourceCount) errs() << "\tFind Toffoli Gate.\n";
              FunctionResources[F][All_]++;
              FunctionResources[F][Toffoli_]++;
            }else if(callee->getName().find("llvm.Fredkin") != std::string::npos){
              if(debugResourceCount) errs() << "\tFind Fredkin Gate.\n";
              FunctionResources[F][All_]++;
              FunctionResources[F][Fredkin_]++;              
            }
          //}
          else if(CI->getCalledFunction()->getName().find("afree") != std::string::npos){
            if(debugResourceCount) errs() << "\tBegin free...\n";
            if(debugResourceCount) errs() << "\tName: " << CI->getArgOperand(0)->getName() << "\n";
            uint64_t addNum = 0;
            if (llvm::ConstantInt* consInt = dyn_cast<llvm::ConstantInt>(CI->getArgOperand(1))){
              addNum = consInt -> getLimitedValue();
              errs() << "This Is The Value: " << addNum;
            }else{
              addNum = 1;
            }
            FunctionResources[F][Net_A_] -= addNum;
            errs() << "Net Then Width" << FunctionResources[F][Net_A_] << " " << FunctionResources[F][Width_] << "\n"; 
            if(debugResourceCount) errs() << "Finish free.\n";
          }else{
            /* Non-intrinsic Function Call. */
          }

        // /* Qubits? */
        // /* Filter Allocation Instructions. */
        // if (AllocaInst *AI = dyn_cast<AllocaInst>(Inst)) {
        //   Type *allocatedType = AI->getAllocatedType();
        //   Type *intType = NULL;
        //   uint64_t arraySize=0;

        //   if(debugResourceCount){
        //     errs() << allocatedType->getTypeID() << " allocated: ";
        //     errs() << "Does it have a name? " << AI->getName() << "\n";
        //   }

        //   /* Filter allocation of arrays. */
        //   if (ArrayType *arrayType = dyn_cast<ArrayType>(allocatedType)) {
        //     Type *elementType = arrayType->getElementType();

        //     if(debugResourceCount) errs() << "dyncasted to array\n";
        //     if(elementType->isIntegerTy(8) || elementType->isIntegerTy(16)){

        //       if(debugResourceCount) errs() << "inside ifstatement\n";///////////////////////////////////////////////////////////////////////////

        //       intType = elementType;
        //       arraySize = arrayType->getNumElements();

        //       if(debugResourceCount) errs() << arraySize << "elements\n";
        //     }
        //   }else{
        //     if(allocatedType->isIntegerTy(8) || allocatedType->isIntegerTy(16)){
        //       intType = allocatedType;
        //       arraySize = 1;
        //     }
        //   } 

        //   /* Filter allocation type(qbit = i16). */
        //   if(intType){
        //     if(intType->isIntegerTy(16)) {
        //       FunctionResources[F][Qbits_] += arraySize;
        //     }
        //     if(intType->isIntegerTy(8)){
        //       FunctionResources[F][Gross_A_] += arraySize;
        //       FunctionResources[F][Net_A_] += arraySize;
        //       if(FunctionResources[F][Width_] < FunctionResources[F][Net_A_])
        //         FunctionResources[F][Width_] = FunctionResources[F][Net_A_];
        //     }
        //   } //End of if allocated instruction
        // }else if (CallInst *CI = dyn_cast<CallInst>(Inst)) {
        //   /* Gates */
        //   /* Filter Call Instruction. */
        //   Function *callee = CI->getCalledFunction();
        //   /* Intrincsic(Gate) Functions Calls. */
        //   // if (callee->isIntrinsic()) {
        //   if (callee->getName().find("llvm.X")){
        //     FunctionResources[F][14]++;
        //     FunctionResources[F][4]++;
        //   }
        //   else if (callee->getName().find("llvm.Z"))
        //     FunctionResources[F][5]++;
        //   else if (callee->getName().find("llvm.H"))
        //     FunctionResources[F][6]++;
        //   else if (callee->getName().find("llvm.Tdag")) {
        //     FunctionResources[F][8]++;
        //     if(debugResourceCount) errs() << "CI: " << *CI << "\n";
        //     if(debugResourceCount) errs() << "Tcount = " << FunctionResources[F][4] << "\n";
        //   }else if(callee->getName().find("llvm.T"))
        //     FunctionResources[F][7]++;
        //   else if (callee->getName().find("llvm.Sdag"))
        //     FunctionResources[F][10]++;
        //   else if (callee->getName().find("llvm.S"))
        //     FunctionResources[F][9]++;
        //   else if (callee->getName().find("llvm.CNOT"))
        //     FunctionResources[F][11]++;            
        //   else if (callee->getName().find("llvm.PrepZ"))
        //     FunctionResources[F][12]++;
        //   else if (callee->getName().find("llvm.MeasZ"))
        //     FunctionResources[F][13]++;
        //   else if(CI->getCalledFunction()->getName().find("afree")){
        //     if(debugResourceCount) errs() << "begin free\n";
        //     //Type *toAdd = (CI -> getArgOperand(0) -> getType());
        //     if(debugResourceCount) errs() << "name: " << CI->getArgOperand(0)->getName() << "\n";
        //     uint64_t addNum=0;
        //     if (llvm::ConstantInt* consInt = dyn_cast<llvm::ConstantInt>(CI->getArgOperand(1))){
        //         addNum = consInt -> getLimitedValue();
        //         errs() << addNum << "this is the value\n";
        //     }else{
        //       addNum = 1;
        //     }
        //     FunctionResources[F][2] -= addNum;
        //     errs() << "net then width" << FunctionResources[F][2] << FunctionResources[F][3] << "\n"; 
        //     if(debugResourceCount) errs() << "finish free\n";
        //   }else{  // Non-intrinsic Function Calls
        //     // Resource numbers must be previously entered
        //     // for this call. Look them up and add to this function's numbers.
        //     if (FunctionResources.find(callee) != FunctionResources.end()) {
        //       unsigned long long* callee_numbers = FunctionResources.find(callee)->second;
        //       FunctionResources[F][14] += callee_numbers[14];
        //       if(callee_numbers[3] > FunctionResources[F][3] - FunctionResources[F][2])
        //         FunctionResources[F][3] = FunctionResources[F][2] + callee_numbers[3];
        //       for (int l=0; l<NCOUNTS; l++)
        //         if(l!=3)
        //           FunctionResources[F][l] += callee_numbers[l];
        //     }
        //   } // else a non-intrinsic function call
        // } // end of call instruction
        // here, we would want to detect the getelement
      } // end of for each instruction
    } // end of procedure
    }

    virtual bool runOnModule (Module &M) {
      // Function* ---> Qubits | Gross Abits | Net Abits | Max Abit Width | X | Z | H | T | CNOT | Toffoli | PrepZ | MeasZ | Rz | Ry
      std::map <Function*, unsigned long long*> FunctionResources;
      std::map <Function*, unsigned long long> FunctionTotals;
  	  std::vector<Function*> callStack;
	    app_total_gates = 0;

      // iterate over all functions, and over all instructions in those functions
      // find call sites that have constant integer values. In Post-Order.
      CallGraphNode* rootNode = getAnalysis<CallGraph>().getRoot();
      
      //fill in the gate count bottom-up in the call graph
      for (scc_iterator<CallGraphNode*> sccIb = scc_begin(rootNode), E = scc_end(rootNode); sccIb != E; ++sccIb) {
        const std::vector<CallGraphNode*> &nextSCC = *sccIb;
        for (std::vector<CallGraphNode*>::const_iterator nsccI = nextSCC.begin(), E = nextSCC.end(); nsccI != E; ++nsccI) {
          Function *F = (*nsccI)->getFunction();	  
          if (F && !F->isDeclaration()) {
            // dynamically create array holding gate numbers for this function
            unsigned long long* ResourceNumbers = new unsigned long long[NCOUNTS+1];
            for (int k=0; k<NCOUNTS+1; k++)
              ResourceNumbers[k] = 0;
            errs() <<F->getName()<<"\n";
            FunctionResources.insert(std::make_pair(F, ResourceNumbers));
            // count the gates of this function 
            CountFunctionResources(F, FunctionResources);
          }
        }
      }
      
      /* Print results. */
      errs() << "\tQubit\tGross A\tNet A\tWidth\tX\tY\tZ\tH\tT\tT_dag\tS\tS_dag\tCNOT\tPrepX\tPrepZ\tMeasX\tMeasZ\tRx\tRy\tRz\tToffoli\tFredkin\n";
      for (std::map<Function*, unsigned long long*>::iterator i = FunctionResources.begin(), 
        e = FunctionResources.end(); i!=e; ++i) {
        errs() << "Function: " << i->first->getName() << "\n";
	      unsigned long long function_total_gates = 0;
        for (int j=0; j<NCOUNTS; j++){
          if(j > 3) function_total_gates += (i->second)[j];
          errs() << "\t" << (i->second)[j];
	  	  }
        if(i->first->getName() == "main") app_total_gates = function_total_gates;
        errs() << "\n";
        errs() << function_total_gates <<"\n"; //<< " \t";
      }
      errs() << "total_gates = "<< app_total_gates << "\n";

      /* Free Memory. */
      for (std::map<Function*, unsigned long long*>::iterator i = FunctionResources.begin(), 
        e = FunctionResources.end(); i!=e; ++i)
        delete [] i->second;
      return false;
    } // End runOnModule
  }; // End of struct ResourceCount2
} // End of anonymous namespace

char ResourceCount::ID = 0;
static RegisterPass<ResourceCount> X("ResourceCount", "Resource Counter Pass");


