#include "RemoveInstrumentations.h"
#include "probe_helper.h"
#include <llvm/IR/PassManager.h>
#include <llvm/Passes/PassBuilder.h>
#include <llvm/Passes/PassPlugin.h>

using namespace llvm;
llvm::PreservedAnalyses RemoveInstrumentations::run(llvm::Function &F, llvm::FunctionAnalysisManager &AM)
{
    remove_instrumentations(F);
    return llvm::PreservedAnalyses::none();
}
extern "C" LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo llvmGetPassPluginInfo()
{
    return {LLVM_PLUGIN_API_VERSION, "RemoveInstrumentations", LLVM_VERSION_STRING, [](PassBuilder &PB) {
                PB.registerPipelineParsingCallback(
                    [](StringRef Name, llvm::FunctionPassManager &PM, ArrayRef<llvm::PassBuilder::PipelineElement>) {
                        if (Name == "remove-instrumentations")
                        {
                            PM.addPass(RemoveInstrumentations());
                            return true;
                        }
                        return false;
                    });
                PB.registerVectorizerStartEPCallback([](llvm::FunctionPassManager &FPM, llvm::OptimizationLevel O) {
                    FPM.addPass(RemoveInstrumentations());
                });
            }};
}