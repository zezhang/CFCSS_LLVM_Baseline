//basic implemented idea is from CFCSS

#define DEBUG_TYPE "cfcss"

#include <map>
#include <set>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <sys/stat.h>

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/Analysis/Passes.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/IntervalPartition.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/ADT/IndexedMap.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Transforms/Instrumentation.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"


#include "llvm/Support/raw_ostream.h"

using namespace llvm;

namespace {
	class CFCSS : public ModulePass {
	public:
		static char ID;
    static bool flag;
    static uint32_t noOfBBs;
    bool runOnModule(Module &M);
    //static IntervalPartition* IP;
    //static LoopInfo* LI;
    /*void getAnalysisUsage(AnalysisUsage &AU) const {
      AU.addRequired<IntervalPartition>();
      AU.addRequired<LoopInfo>();
    }*/
    CFCSS() : ModulePass(ID){}
	private:
	  std::map<BasicBlock*, uint32_t> BBToSig; //first signature should start with 1
    //std::set<BasicBlock*> branchFanInNodes;
    std::map<BasicBlock*, Instruction*> BBToInsertPt;
    std::map<Function*, BasicBlock*> FunctionToExitBlock;
    std::map<Function*, Value*> FunctionToGlobalName;
    GlobalVariable* gSig;
    Constant* printFun;
    Constant* gvar_ptr_stderr;
    //functions are implemented here
    bool isThisBranchFanIn(BasicBlock* bb);
    void addSigDifference(BasicBlock* bb);
    void handleBranchFanIn(BasicBlock* bb);
    Instruction* getLocalVar(BasicBlock* bb, Instruction* insrtPt, uint32_t sig1, uint32_t sig2);
    void insertWriteToFileFunction(Module* mod);
    void insertMsgFunCall();
    void addPrintFun(Function* FunPtr);
    BasicBlock* getExitBlock(Function* FunPtr, Function* currF);
	};
	//end of class
}
//end of namespace

char CFCSS::ID = 0;
bool CFCSS::flag = false;
uint32_t CFCSS::noOfBBs = 0;
//IntervalPartition* CFCSS::IP = 0;
//LoopInfo* CFCSS::LI = 0;

static RegisterPass<CFCSS> Y("cfcss", "CFCSS Implementation");

bool CFCSS::runOnModule(Module &M){
	if(flag == true){
    	return false;
 	}

  //load the error function
  Function* hookFabs = M.getFunction("find_err");
  if(!hookFabs){
    errs() << "Function fabs is not found\n";
    exit(-1);
  }


 	//actual implementation goes here
 	//clear and initialize all variables
 	BBToSig.clear();
 	//branchFanInNodes.clear();
 	BBToInsertPt.clear();
 	FunctionToExitBlock.clear();
 	FunctionToGlobalName.clear();
 	gSig = NULL;
 	printFun = NULL;
 	gvar_ptr_stderr = NULL;

 	//declare a global variable for global signature (gSig)
 	GlobalVariable* sigVar = new GlobalVariable(M, 
             IntegerType::get(M.getContext(), 32),
             false,
             GlobalValue::ExternalLinkage,
             0,
             "gSig");
 	ConstantInt* const_int32_8 = ConstantInt::get(M.getContext(), APInt(32, StringRef("0"), 10));
 	sigVar->setInitializer(const_int32_8);
 	gSig = sigVar;

 	//assign a static signature to each basic block, ingore the interval optimization for now
 	for(Module::iterator I = M.begin(), E = M.end(); I != E; ++I){
 		if(!I->isDeclaration()) {
 			for(Function::iterator bb_iter = I->begin(); bb_iter != I->end(); ++bb_iter){
        		BasicBlock* bb = &(*bb_iter);
        		DEBUG(dbgs() << " Current bb name " << bb->getName() << " in function " << bb->getParent()->getName() << "\n");
        		BBToSig[bb] = ++noOfBBs;
        	}
 		}
 	}

  for(Module::iterator I = M.begin(), E = M.end(); I != E; ++I){
    if(!I->isDeclaration()) {
      DEBUG(dbgs() << I->getName() << "\n");
    }
  }
 	DEBUG(dbgs() << "No of total basic blocks are: " << noOfBBs << "\n");

 	//add the static signature difference and also output(debug)
 	for(std::map<BasicBlock*, uint32_t>::iterator iter = BBToSig.begin();
      	iter != BBToSig.end(); iter++){
	    BasicBlock* curBB = iter->first;
	    uint32_t curSig = iter->second;
	    DEBUG(dbgs() << "for BB " << curBB->getName()  << " in " <<curBB->getParent()->getName()<< " signature is " << curSig << "\n");
	    addSigDifference(curBB);
	    //intervalDebugExplore();
  }

  DEBUG(dbgs() << "Finished adding the signature difference!!!!\n");

  //add the print function--Not sure if this will work
  //addPrintFun(hookFabs);
  for(std::map<BasicBlock*, Instruction*>::iterator iter = BBToInsertPt.begin(); iter != BBToInsertPt.end(); iter++){
    //BasicBlock::iterator splitIt = ++(static_cast<BasicBlock::iterator>(iter->second));
    Instruction* cmpInst = (iter->second);
    TerminatorInst *CFExitBB = SplitBlockAndInsertIfThen((Value*)cmpInst, cmpInst->getNextNode(), true);
    //BasicBlock* oldBB = cmpInst->getParent();
    //BasicBlock* newBB = oldBB->splitBasicBlock(splitIt);
    //Function* currF = oldBB->getParent();
    //BasicBlock* CFExitBB = BasicBlock::Create(currF->getContext());
    //Instruction* termInst = oldBB->getTerminator();
    //BranchInst* condBr = BranchInst::Create(CFExitBB, newBB, (Value*)cmpInst, oldBB);
    //termInst->eraseFromParent();
    //add the printf_err function in the new basicblock
    IRBuilder<> Builder(CFExitBB);
    Builder.CreateCall(hookFabs);
  }

 	flag = true;
 	return false;
}

bool CFCSS::isThisBranchFanIn(BasicBlock* bb){
  if(bb->getUniquePredecessor() != NULL){
    return false;
  }
  return true;
}

void CFCSS::handleBranchFanIn(BasicBlock* bb){
	//if the current node is a branch fanin node, take special care
 bool isFirstPred = true;
 uint32_t firstBBSig = 0;
 std::multimap<BasicBlock*, Value*> BBToDVal;

	DEBUG(dbgs() << "#### Processing " << bb->getName() << " in " << bb->getParent()->getName() << " ####\n");
	DEBUG(dbgs() << "     signature " << BBToSig[bb] << "\n");
	//go through each pred of the current branch fanin node, find the xor value with the first pred node
	for(pred_iterator PI = pred_begin(bb); PI != pred_end(bb); ++PI){
		BasicBlock* predBB = *PI;
		DEBUG(dbgs() << "\t predecessor " << predBB->getName() << "\n");
		Instruction* InsertPt;
		if(BBToInsertPt.find(predBB) != BBToInsertPt.end()){
  		InsertPt = BBToInsertPt[predBB];
  		//InsertPt++;
    }
    else{
    	//NOTE:could have bug here!!!! use static_cast
      InsertPt = (Instruction*)(predBB->getFirstNonPHI());
    }
    IRBuilder<> Builder(InsertPt);
    if(isFirstPred){
  		//choose the first block to store 0 to DSig
  		firstBBSig = BBToSig[predBB];
  		DEBUG(dbgs() << "\t signature " << firstBBSig << "\n");
      Instruction* xr = getLocalVar(predBB, InsertPt, firstBBSig, firstBBSig);
      //DEBUG(dbgs() << "ZE_________________xr instruction is at " << xr->getParent()->getName() << "\n");
      BBToDVal.insert(std::pair<BasicBlock*, Value*>(predBB, (Value*)xr));
  		isFirstPred = false;
    }
    else {
    	//for all other preds except the first one
    	uint32_t currSig = BBToSig[predBB];
    	DEBUG(dbgs() << "\t signature " << currSig << "\n");
    	Instruction* xr = getLocalVar(predBB, InsertPt, firstBBSig, currSig);
      //DEBUG(dbgs() << "ZE_________________xr instruction is at " << xr->getParent()->getName() << "\n");
    	BBToDVal.insert(std::pair<BasicBlock*, Value*>(predBB, (Value*)xr));
    }
	}
  	//add all Dvalues to a PHI node since don't know which edge is coming
  	Instruction* InsertPt = (Instruction*)(bb->getFirstNonPHI());
  	IRBuilder<> Builder(InsertPt);
  	//NOTE:could be wrong here since no getGlobalContext() function
  	/*LLVMContext *ctext;
  	LLVMContext MyGlobalContext;
  	ctext = &MyGlobalContext;
  	PHINode *PN = Builder.CreatePHI(Type::getInt32Ty(*ctext), 0,"D");*/

  	LLVMContext &ctxt = bb->getParent()->getContext();
  	PHINode *PN = Builder.CreatePHI(Type::getInt32Ty(ctxt), 0,"D");
	for(std::multimap<BasicBlock*, Value*>::iterator iter = BBToDVal.begin(); iter != BBToDVal.end(); iter++){
		PN->addIncoming(iter->second, iter->first);
	}

	//compare and xor values in the phi node
	uint32_t currSig = BBToSig[bb];
	uint32_t sigDiff = firstBBSig ^ currSig;
	LoadInst* G = Builder.CreateLoad(gSig);
	Value* xorInst = Builder.CreateXor(G, sigDiff);
	Value* xorInst_D = Builder.CreateXor(xorInst, PN);
	//check the result
	Value* currSigConst = ConstantInt::get(xorInst_D->getType(), currSig);
  Value* cmpInst = Builder.CreateICmpNE(xorInst_D, currSigConst);
  //BasicBlock::iterator cmpIt((Instruction*)cmpInst);
  //remember the current place. add more insns later
  BBToInsertPt[bb] = (Instruction*)cmpInst;

  //update the gSig at last
  Builder.SetInsertPoint(bb->getTerminator());
	Builder.CreateStore(xorInst_D, gSig);
}

Instruction* CFCSS::getLocalVar(BasicBlock* bb, Instruction* insrtPt, uint32_t sig1, uint32_t sig2){
  IRBuilder<> Builder(insrtPt);
  //NOTE:could have bug here!!!!no getGlobalContext() function
  /*LLVMContext *ctext;
  LLVMContext MyGlobalContext;
  ctext = &MyGlobalContext;
  Type* uintTp = Type::getInt32Ty(*ctext);*/
  //DEBUG(dbgs() << "ZE_________________insrtPt instruction is at " << insrtPt->getParent()->getParent()->getName() << "\n");
  LLVMContext &ctxt = bb->getParent()->getContext();
  Type* uintTp = Type::getInt32Ty(ctxt);

  Value *constSig1 = ConstantInt::get(uintTp, sig1);
  Value *constSig2 = ConstantInt::get(uintTp, sig2);
  Instruction* Inst = (Instruction*)(Builder.CreateXor(constSig1, constSig2, "D"));
  //DEBUG(dbgs() << "ZE_________________Inst instruction is at " << Inst->getParent()->getParent()->getName() << "\n");
  return Inst;
}

void CFCSS::addSigDifference(BasicBlock* bb){
	//for the entry node, just assign the the current node signature to the gSig
	//NOTE: static_cast in the following line could cause BUG!!!!
	Instruction* InsertPt = (Instruction*)(bb->getFirstNonPHI());
	IRBuilder<> Builder(InsertPt);
	if(pred_begin(bb) == pred_end(bb)) {
		  uint32_t currSig = BBToSig[bb];
		  LLVMContext &ctxt = bb->getParent()->getContext();
    	Type* uintTp = Type::getInt32Ty(ctxt);
    	Value *constSig = ConstantInt::get(uintTp, currSig);
    	Builder.SetInsertPoint(bb->getTerminator());
    	Builder.CreateStore(constSig, gSig);
    	return;
	}
	//for branchin node and not the entry node
	if(isThisBranchFanIn(bb)) {
		  //handle branch fanin node
		  handleBranchFanIn(bb);
	}
	else {
  		//for non branch in node
  		DEBUG(dbgs() << bb->getName() << " is not a branch fan in node"<< "\n");
  		BasicBlock* predBB = bb->getUniquePredecessor();
  		//calculate the static signature difference
  		uint32_t predSig = BBToSig[predBB];
    	uint32_t currSig = BBToSig[bb];
    	uint32_t sigDiff = predSig ^ currSig;
    	//load the global variable gSig
    	LoadInst* G = Builder.CreateLoad(gSig);
    	//xor the static difference with gSig
    	Value* xorInst = Builder.CreateXor(G, sigDiff);
    	//insert the compare instruction
    	Value* currSigConst = ConstantInt::get(xorInst->getType(), currSig);
    	Value* cmpInst = Builder.CreateICmpNE(xorInst, currSigConst);
    	//BasicBlock::iterator cmpIt((Instruction*)cmpInst);
    	//remember the current place. add more insns later
    	BBToInsertPt[bb] = (Instruction*)cmpInst;

    	//update the gSig at last
    	Builder.SetInsertPoint(bb->getTerminator());
    	Builder.CreateStore(xorInst, gSig);
	}
}
