#pragma once
#include "llvm/IR/PassManager.h"
#include <string>
#include <unordered_map>

class DetectZeroPass : public llvm::PassInfoMixin<DetectZeroPass>
{
    using string = std::string;

private:
    std::unordered_map<const llvm::Value *, const llvm::DILocalVariable *> metadata_map;

    llvm::PreservedAnalyses _run(llvm::Function &F, llvm::FunctionAnalysisManager &AM);

public:
    llvm::PreservedAnalyses run(llvm::Function &F, llvm::FunctionAnalysisManager &AM);
};