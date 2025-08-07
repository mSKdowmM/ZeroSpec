#pragma once
#include <llvm/IR/PassManager.h>
class RemoveInstrumentations : public llvm::PassInfoMixin<RemoveInstrumentations>
{
public:
    llvm::PreservedAnalyses run(llvm::Function &F, llvm::FunctionAnalysisManager &AM);
};