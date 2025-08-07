#!/usr/bin/env python3
from glob import glob
import sys
import os
# info_dir = '/mnt/ssd2/dsk/spec2017/benchspec/CPU/544.nab_r/src'
# info_dir = '/mnt/ssd2/dsk/spec2017/benchspec/CPU/549.fotonik3d_r/build/build_base_mytest-m64.0000'
if (len(sys.argv) < 2):
    # print(f'Usage: {sys.argv[0]} data_dir')
    # sys.exit(1)

    # data_dir is latest created directory named "data-*"
    data_dir = max(glob('data-*'), key=os.path.getctime)
else:
    data_dir = sys.argv[1]
# info_dirs = list(sys.argv[2:])
info_dirs = [os.getcwd(), '/']
if len(sys.argv) >= 3:
    info_dirs = [ sys.argv[2] ] + info_dirs

def find_info(info_dirs:"list[str]", file_name):
    # checkout whether the file exists in the info_dirs
    for d in info_dirs:
        # print(f'{d}/{file_name}')
        if os.path.exists(f'{d}/{file_name}'):
            return d
    return None
if os.path.isdir(data_dir):
    data_files = glob(f'{data_dir}/*')
    # tids = list(set([int(x.split('-')[-1]) for x in data_files]))
    data_files = [x  for x in data_files if '/func-map-' in x]
else:
    data_files = []
    with open(f'{data_dir}') as f:
        for l in f:
            data_files += list(glob(f'{l.strip()}/*'))
    data_files = [x  for x in data_files if '/func-map-' in x]


class DbgInfoManager():
    def __init__(self):
        self.dbg_info_d = {}
    def get(self, source_name, func_name):
        if source_name in self.dbg_info_d:
            return self.dbg_info_d[source_name][func_name]
        info_dir = find_info(info_dirs, f'{source_name}.info')
        with open(f'{info_dir}/{source_name}.info') as f:
            info = f.readlines()
            info = [x.strip() for x in info]
        define_pos = source_name
        self.dbg_info_d[source_name] = {}
        for l in info:
            if l.startswith('[FUNCTION]'):
                # print(l)
                r=  l.split(':')
                if len(r) == 4:
                    _, name, linkage_name, define_pos = r 
                else:
                    _, name, linkage_name  = r
                if linkage_name == '':
                    real_name = name
                else:
                    real_name = linkage_name
                self.dbg_info_d[source_name][real_name] = []
            else:
                self.dbg_info_d[source_name][real_name].append(DbgInfo(*l.split(':')))
        return self.dbg_info_d[source_name][func_name]
class DbgInfo():
    """compile time debug info for a instrumentation position
    """
    def __init__(self, func_id, line, column, linkage_name, raw_name, def_pos, benefit):
        """_summary_

        Args:
            func_id (int): function id
            line (int): line
            column (int): column
            linkage_name (str): _description_
            raw_name (str): _description_
            def_pos (str): function may define at a header file, which means the source file is not the same as the function definition file
        """
        self.func_id = int(func_id)
        self.line = int(line)
        self.column = int(column)
        self.linkage_name = linkage_name
        self.raw_name = raw_name
        self.def_pos = def_pos
        self.benefit = int(benefit)
zero_type_map = {
    -1: 'unknown',
    0: 'int',
    1: 'float',
    2: 'double',
    4294967295: 'unknown'
}
class ZeroInfo():
    """run time zero info for a instrumentation position
    """
    def __init__(self, offset, total_count, zero_count, zero_type, predict_hit_count=-1):
        self.offset = int(offset)
        self.total_count = int(total_count)
        self.zero_count = int(zero_count)
        self.predict_hit_count = int(predict_hit_count)
        if type(zero_type) == type(0) or zero_type.isdigit():
            self.zero_type = zero_type_map[int(zero_type)]
        else:
            self.zero_type = zero_type
    def clone(self):
        return ZeroInfo(self.offset, self.total_count, self.zero_count, self.zero_type, self.predict_hit_count)
class FuncInfo():
    """run time function info for a set of instrumentation positions
    """
    def __init__(self, source, func, offset):
        self.source = source
        self.func = func
        self.offset = int(offset)
class Record():
    def __init__(self, dbg_info: DbgInfo, zero_info: ZeroInfo, func_info: FuncInfo):
        self.dbg_info = dbg_info
        self.zero_info = zero_info
        self.func_info = func_info
        assert(self.dbg_info.func_id == self.zero_info.offset - self.func_info.offset)
    def zero_ratio(self):
        return self.zero_info.zero_count / self.zero_info.total_count
    def pos(self):
        if self.dbg_info.def_pos == '':
            return f'+ {self.func_info.source}:{self.dbg_info.line}:{self.dbg_info.column} {self.func_info.func}'
        return f'{self.dbg_info.def_pos}:{self.dbg_info.line}:{self.dbg_info.column} {self.func_info.func}'
    def identity(self):
        return f'{self.pos()} {self.dbg_info.raw_name} {self.zero_info.offset - self.func_info.offset}'
    def instrument_id(self):
        return self.zero_info.offset - self.func_info.offset
    def is_empty(self):
        return self.pos() == self.zero().pos()
    def is_same(self, r: "Record"):
        return self.pos() == r.pos() or self.is_empty() or r.is_empty()
    def clone(self):
        return Record(self.dbg_info, self.zero_info.clone(), self.func_info)
    # def __addeq__(self, r: "Record"):
    #     assert(self.is_same(r))
    #     self.zero_info.total_count += r.zero_info.total_count
    #     self.zero_info.zero_count += r.zero_info.zero_count
    #     if self.is_empty():
    #         self.func_info = r.func_info
    #         self.dbg_info = r.dbg_info
    def __add__(self, r: "Record"):
        assert(self.is_same(r))
        res = self.clone()
        res.zero_info.total_count += r.zero_info.total_count
        res.zero_info.zero_count += r.zero_info.zero_count
        res.zero_info.predict_hit_count += r.zero_info.predict_hit_count
        if res.is_empty():
            res.func_info = r.func_info
            res.dbg_info = r.dbg_info
            res.zero_info.offset = r.zero_info.offset
            res.dbg_info.benefit = max(r.dbg_info.benefit, res.dbg_info.benefit)
            res.zero_info.zero_type = r.zero_info.zero_type
        return res
    @staticmethod
    def zero():
        return Record(DbgInfo(0, 0, 0, "", "", "", -1), ZeroInfo(0,0,0,-1,0), FuncInfo("", "", 0))

def filter_file(lines):
    if len(lines) == 0:
        return []
    st = lines.index('[REPORT BEGIN]\n') 
    ed = lines.index('[REPORT END]\n')
    return lines[st+1:ed]
records = [] 
dbg_info_manager = DbgInfoManager()
# for tid in tids:
for func_map_file in data_files:
    zero_map_file = func_map_file.replace('func-map', 'zero')
    # with open(f'{data_dir}/zero-{tid}') as fz, open(f'{data_dir}/func-map-{tid}') as ff:
    with open(zero_map_file) as fz, open(func_map_file) as ff:
        zeros = fz.readlines()
        func_map = ff.readlines()
        try:
            zeros = filter_file(zeros)
            func_map = filter_file(func_map)
        except(Exception) as e:
            print(f'Error: {zero_map_file} {func_map_file}')
            raise e
            exit(1)
    # print(zero_map_file, func_map_file)
    func_map = [x.strip().split(':') for x in func_map]
    func_map = [FuncInfo(*x) for x in func_map]
    func_map.append(FuncInfo(None, None, len(zeros)))
    func_map.sort(key=lambda x:x.offset)
    zeros = [ZeroInfo(*x.strip().split(' ')) for x in zeros]
    for i, item in enumerate(func_map[:-1]):
        # with open(f'{info_dir}/{func_map[i].func}.info') as fi:
        #     info = fi.readlines()
        #     info = [x.strip().split(':') for x in info]
        #     info = [DbgInfo(*x) for x in info]
        info = dbg_info_manager.get(func_map[i].source, func_map[i].func)
        for j in range(func_map[i].offset, func_map[i+1].offset):
            # print(j, zeros[j].offset, info[j-func_map[i].offset].func_id)
            # print(len(info), j-func_map[i].offset, func_map[i].offset, func_map[i+1].offset)
            if j - func_map[i].offset >= len(info):
                records.append(Record(DbgInfo(i, -1, -1, info[0].linkage_name, info[0].raw_name, info[0].def_pos, -1), zeros[j], func_map[i]))
                # continue
            else:
                records.append(Record(info[j-func_map[i].offset], zeros[j], func_map[i]))
records = [x for x in records if x.zero_info.zero_count != 0]
records.sort(key=lambda x: x.zero_ratio() *(x.zero_info.total_count), reverse=True)
records1 = {}

for r in records:
    records1.setdefault(r.identity(), [])
    records1[r.identity()].append(r)
    
    # print(sum([Record.zero(),r], Record.zero()).identity())
    # print(f'{r.identity()} {r.zero_ratio()} {r.zero_info.total_count}')
records2 = [sum(records1[x], Record.zero()) for x in records1]

records2.sort(key=lambda x: x.zero_ratio() *(x.zero_info.total_count) * (x.dbg_info.benefit + 1), reverse=True)
print('-----------------')
print('position func_name raw_name zero_ratio total_count')
# for r in records2:
for r in records2[:100]:
    print(f'{r.identity()} {r.zero_ratio()} {r.zero_info.total_count} {r.zero_info.zero_type} {r.dbg_info.benefit}')
print(Record.zero().is_empty())

benefit_map = {}
with open('zero.report', 'w') as f:
    for r in records2:
        benefit_map.setdefault(r.dbg_info.benefit, [0, 0])
        benefit_map[r.dbg_info.benefit][0] += 1
        benefit_map[r.dbg_info.benefit][1] += r.zero_info.total_count
        res = f'{r.func_info.source}:{r.func_info.func} {r.instrument_id()} {r.zero_ratio()} {r.zero_info.total_count} {r.zero_info.zero_type} {r.dbg_info.benefit} {r.zero_info.predict_hit_count}\n'
        res.replace('+ ', '')
        f.write(res)
pos_count = sum([x[0] for x in benefit_map.values()])
run_count = sum([x[1] for x in benefit_map.values()])
for k in sorted(benefit_map.keys(), key=lambda x: benefit_map[x][1], reverse=True):
    print(f'Benefit {k}: {benefit_map[k][0]} {benefit_map[k][1]} {benefit_map[k][0]/pos_count} {benefit_map[k][1]/run_count}')