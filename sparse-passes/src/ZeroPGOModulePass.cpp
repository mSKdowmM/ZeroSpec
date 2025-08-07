#include <ZeroPGOModulePass.h>
#include "InstDestClassification.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Passes/PassBuilder.h"
#include <DetectZeroPass.h>
#include <filesystem>
llvm::PreservedAnalyses ZeroPGOModulePass::run(llvm::Module &M, llvm::ModuleAnalysisManager &mam)
{
    bool Changed = runOnModule(M);
    return (Changed ? llvm::PreservedAnalyses::none() : llvm::PreservedAnalyses::all());
}

bool ZeroPGOModulePass::runOnModule(llvm::Module &M)
{
    auto module_path_str = M.getSourceFileName();
    std::filesystem::path module_path(module_path_str);
    module_path.replace_extension(".ll");
    FILE *f = fopen(module_path.c_str(), "w");
    llvm::raw_fd_ostream stream(fileno(f), true);
    M.print(stream, nullptr);
    return true;
}

extern "C" LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo llvmGetPassPluginInfo()
{
    using namespace llvm;
    return {LLVM_PLUGIN_API_VERSION, "ZeroPGO", LLVM_VERSION_STRING, [](PassBuilder &PB) {
                PB.registerAnalysisRegistrationCallback(
                    [](FunctionAnalysisManager &AM) { AM.registerPass([&] { return InstDestClassification(); }); });
                PB.registerOptimizerLastEPCallback([](llvm::ModulePassManager &MPM, llvm::OptimizationLevel O) {
                    MPM.addPass(createModuleToFunctionPassAdaptor(DetectZeroPass()));
                    MPM.addPass(ZeroPGOModulePass());
                });
            }};
}
