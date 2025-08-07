#!/usr/bin/env python3
import re
import subprocess
import sys
import os
import fcntl
import timeit

all_args = sys.argv[1:]
init_args = list(all_args)

cc = 'clang++'
while '--use-clang' in all_args:
    all_args.remove('--use-clang')
    cc = 'clang'
while '--use-flang' in all_args:
    all_args.remove('--use-flang')
    cc = 'flang-new'

lib_path = os.getenv('ZERO_SPEC_LIB_DIR')

def write_log(msg, identifier):
    file_name = '/dev/null'
    if os.getenv('ZERO_SPEC_TIMER_LOG') is not None:
        file_name = os.getenv('ZERO_SPEC_TIMER_LOG')
    with open(file_name, 'a') as f:
        fcntl.flock(f, fcntl.LOCK_EX)
        f.write(f'[{identifier}]: {msg}\n')
        fcntl.flock(f, fcntl.LOCK_UN)

def run(args,enable_fail=False, **kwargs):
    cmd = ' '.join(args)
    print(cmd, flush=True)
    st = timeit.default_timer()
    res = subprocess.run(args, stdout=sys.stdout, stderr=subprocess.PIPE, **kwargs)
    ed = timeit.default_timer()
    print(res.stderr.decode(), flush=True, file=sys.stderr)
    if not enable_fail and res.returncode != 0:
        exit(res)
    if args[0] == 'opt':
        write_log(f'[OPT]: {ed - st}', str(init_args))
    else:
        write_log(f'[CLANG]: {ed - st}', str(init_args))
    
    def get_log(log, keyword, msg):
        if keyword in log:
            log = log.split('\n')
            log = [x for x in log if keyword in x]
            log = [x.split(':')[1] for x in log]
            log = [float(x) for x in log]
            write_log(f'{msg}: {sum(log)}', str(init_args))
    get_log(res.stderr.decode(), '[ZeroBenefitAnalysis]', '[ZERO_BENEFIT_ANALYSIS]')
    get_log(res.stderr.decode(), '[INSTR_COUNT]', '[INSTR_COUNT]')
    get_log(res.stderr.decode(), '[BACKWARD_SLICING]', '[BACKWARD_SLICING]')
    
    # if 'ZeroBenefitAnalysis' in str(res.stderr):
    #     raw_log = res.stderr.decode().split('\n')
    #     raw_log = [x for x in raw_log if '[ZeroBenefitAnalysis]' in x]
    #     raw_log = [float(x.split(':')[1]) for x in raw_log]
    #     write_log(f'[ZERO_BENEFIT_ANALYSIS]: {sum(raw_log)}', str(init_args))
    # if 'INSTR_COUNT' in res.stderr.decode():
    #     instr_count = res.stderr.decode().split('\n')
    #     instr_count = [x for x in instr_count if 'INSTR_COUNT' in x]
    #     instr_count = [int(x.split(':')[1]) for x in instr_count]
    #     write_log(f'[INSTR_COUNT]: {sum(instr_count)}', str(init_args))
    return res
def run_pass(pass_name, lib_name, source_file_name, output_file_name, enable_fail=False):
    pass_lib = f'{lib_path}/{lib_name}'
    env = os.environ.copy()
    # env['LD_PRELOAD'] = '/usr/lib/gcc/x86_64-linux-gnu/9/libasan.so'
    return run(['opt'] + [f'-passes={pass_name}'] + [f'--load-pass-plugin={pass_lib}', source_file_name, '-o', output_file_name], enable_fail=enable_fail, env=env)

    


def remove_source_file(args):
    return [arg for arg in args if re.search('\.(c|cpp|f90|bc|cc|cxx|C|f)$', arg) is None]
def filter_args(args):
    return [arg for arg in args if arg not in ['--dump-ir', '--detect-sparse', '--if-zero-opt', '--remove-info', '--remove-isystem', '--use-clang', '--use-flang']]

instrument_link_flag =  f'-L{lib_path} -lprobe -Wl,-rpath={lib_path}'
mode = os.getenv('ZERO_SPEC_MODE')

if mode is None:
    all_args = filter_args(all_args)
    print("NO_ZERO_SPEC_BUILDING",flush=True)
    print (" ".join([cc] + all_args),flush=True)
    run([cc] + all_args)
    # if '-c' in all_args:
    #     all_args = [re.sub('\.o$', '.bc', arg) for arg in all_args]
    #     run([cc] + all_args + '-fno-math-errno -fno-trapping-math -O -emit-llvm -fno-vectorize'.split(' '))
    # else:
    #     all_args = [re.sub('\.o$', '.bc', arg) for arg in all_args]
    #     run([cc] + all_args + '-fno-math-errno -fno-trapping-math -O'.split(' '))
    exit(0)
elif mode == 'DETECT':
    if cc == 'flang-new':
        instrumentation_compile_flags = '-g -O3 -emit-llvm'
    else:
        instrumentation_compile_flags = '-fno-math-errno -fno-trapping-math -g -O3 -emit-llvm' 
    #instrumentation_compile_flags = '-g -O3 -emit-llvm'
    # instrumentation_compile_flags = '-g -O3 -emit-llvm'
    # instrumentation_compile_flags = '-g -O3 -emit-llvm'
    # if 'sf_sfclayrev' not in ' '.join(init_args):
    #     os.environ['DETECT_TARGET_FUNC'] = 'xxxxxxxxxxxxxxxxxxxxxxx'
    if 'MicroBenchmarks' in ' '.join(init_args):
        os.environ['DETECT_TARGET_FUNC'] = 'xxxxxxxxxxxxxxxxxxxxxxx'


    if '-c' in all_args:
        if '--remove-info' in all_args:
            all_args.remove('--remove-info')
            for arg in all_args:
                if os.path.exists(f'{arg}.info'):
                    os.remove(f'{arg}.info')
        if '-o' in all_args:
            idx = all_args.index('-o')
            output_file_name = all_args[idx + 1]
        else:
            source_files = [arg for arg in all_args if os.path.exists(arg)]
            if len(source_files) != 1:
                print('Error: multiple source files')
                exit(1)
            source_file_name = source_files[0]
            output_file_name = re.sub('\.(c|f90|C|f|cpp|cc)$', '.o', source_file_name)
        raw_bc_name = re.sub('\.o$', '.raw.bc', output_file_name)
        instrumented_bc_name = re.sub('\.o$', '.detect.bc', output_file_name)
        raw_all_args = list(all_args)
        if '-o' in all_args:
            idx = raw_all_args.index('-o')
            raw_all_args[idx + 1] = raw_bc_name
        else:
            raw_all_args.append('-o')
            raw_all_args.append(raw_bc_name)
        run([cc] + instrumentation_compile_flags.split(' ') + raw_all_args)
        res = run_pass('detect-zero', 'libDetectZero.so', raw_bc_name, instrumented_bc_name, True)
        if res.returncode != 0:
            os.environ['DETECT_TARGET_FUNC'] = 'xxxxxxxxxxxxxxxxxxxxxxx'
            res = run_pass('detect-zero', 'libDetectZero.so', raw_bc_name, instrumented_bc_name)
            
        all_args = remove_source_file(all_args)
        if '-o' in all_args:
            idx = all_args.index('-o')
            all_args[idx + 1] = output_file_name
        run([cc] + all_args + [instrumented_bc_name])
        # run(['touch', output_file_name])
        exit(0)
    else:
        all_args = filter_args(all_args)
        all_args = [re.sub('\.o$', '.detect.bc', arg) for arg in all_args]
        run([cc] + all_args + instrument_link_flag.split(' '))
        exit(0)
elif mode == 'OPT':
    all_args = filter_args(all_args)
    # if 'sf_sfclayrev' not in ' '.join(init_args):
        # os.environ['DETECT_TARGET_FUNC'] = 'xxxxxxxxxxxxxxxxxxxxxxx'
    # if 'fe_values.cc' in ' '.join(init_args):
    #     os.environ['DETECT_TARGET_FUNC'] = 'xxxxxxxxxxxxxxxxxxxxxxx'
    # if 'ESMF_CalendarMod.fppized.f90' in ' '.join(init_args):
    #     os.environ['DETECT_TARGET_FUNC'] = 'xxxxxxxxxxxxxxxxxxxxxxx'
    #os.environ['DETECT_TARGET_FUNC'] = '_QMphysics_typesPphysics_update'
    # if 'morphology' not in ' '.join(init_args):
        # os.environ['DETECT_TARGET_FUNC'] = 'xxxxxxxxxxxxxxxxxxxxxxx'

    if '-c' in all_args:
        if '-o' in all_args:
            all_args = remove_source_file(all_args)
            output_file_name = all_args[all_args.index('-o') + 1]
        else:
            source_files = [arg for arg in all_args if os.path.exists(arg)]
            if len(source_files) != 1:
                print('Error: multiple source files')
                exit(1)
            source_file_name = source_files[0]
            output_file_name = re.sub('\.(c|cpp|cc|f90|C|f)$', '.o', source_file_name)
        instrumented_bc_name = re.sub('\.o$', '.detect.bc', output_file_name)
        opt_bc_name = re.sub('\.o$', '.opt.bc', output_file_name)
        if not os.getenv('ZERO_SPEC_NO_OPT'):
            res = run_pass('zero-spec-opt', 'libZeroSpecOpt.so', instrumented_bc_name, opt_bc_name, True)
            if res.returncode != 0:
                run_pass('remove-instrumentations', 'libRemoveInstrumentations.so', instrumented_bc_name, opt_bc_name)
            else:
                run_pass('remove-instrumentations', 'libRemoveInstrumentations.so', opt_bc_name, opt_bc_name, True)
            has_optimize_target = '[INFO] has optimize target' in res.stderr.decode()
        else:
            run_pass('remove-instrumentations', 'libRemoveInstrumentations.so', instrumented_bc_name, opt_bc_name)
        if '-o' not in all_args:
            all_args.append('-o')
            all_args.append(output_file_name)
        all_args = remove_source_file(all_args)
        run([cc] + all_args + [opt_bc_name])
        # run([cc] + ['-O2' if x == '-O3' else x for x in all_args] + [opt_bc_name])
        if not has_optimize_target:
            run([cc] + filter_args(init_args))
        exit(0)
    else:
        
        # run([cc] + [re.sub('\.o$', '.opt.bc', x) for x in all_args])
        run([cc] + all_args)
        exit(0)
elif mode == 'TIME':
    instrumentation_compile_flags = '-fno-vectorize -fno-math-errno -fno-trapping-math -g -O -emit-llvm'
    if '-c' in all_args:
        if '--remove-info' in all_args:
            all_args.remove('--remove-info')
            for arg in all_args:
                if os.path.exists(f'{arg}.info'):
                    os.remove(f'{arg}.info')
        if '-o' in all_args:
            idx = all_args.index('-o')
            output_file_name = all_args[idx + 1]
        else:
            source_files = [arg for arg in all_args if os.path.exists(arg)]
            if len(source_files) != 1:
                print('Error: multiple source files')
                exit(1)
            source_file_name = source_files[0]
            output_file_name = re.sub('\.c$', '.detect.bc', source_file_name)
        raw_bc_name = re.sub('\.o$', '.raw.bc', output_file_name)
        instrumented_bc_name = re.sub('\.o$', '.detect.bc', output_file_name)
        raw_all_args = list(all_args)
        if '-o' in all_args:
            idx = raw_all_args.index('-o')
            raw_all_args[idx + 1] = raw_bc_name
        else:
            raw_all_args.append('-o')
            raw_all_args.append(raw_bc_name)
        run([cc] + instrumentation_compile_flags.split(' ') + raw_all_args)
        all_args = remove_source_file(all_args)
        if '-o' in all_args:
            idx = all_args.index('-o')
            all_args[idx + 1] = output_file_name
        run([cc] + all_args + [raw_bc_name])
        exit(0)
    else:
        all_args = filter_args(all_args)
        all_args = [re.sub('\.o$', '.detect.bc', arg) for arg in all_args]
        run([cc] + all_args + instrument_link_flag.split(' '))
        exit(0)
else:
    print(f'ZERO_SPEC_MODE is not set correctly: {mode}')
    exit(1)
        
