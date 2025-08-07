#!/bin/bash
set -e
echo -e "ALL: \c" > Makefile.bcopt
for bc in `find . -name "*.bc" | grep -v -P "\.2\.bc$"`;
do
	prefix=`echo $bc | perl -pe 's/\.bc$//'`
    echo -e "${prefix}.o \c" >> Makefile.bcopt
    echo -e "${prefix}.o: ${prefix}.bc" >> Makefile.bc.tmp
	echo -e "\topt -passes=\"zero-spec-opt\" --load-pass-plugin=${ZERO_SPEC_LIB_DIR}/libZeroSpecOpt.so ${prefix}.bc -o ${prefix}.2.bc" >> Makefile.bc.tmp
	echo -e "\topt -passes=\"remove-instrumentations\" --load-pass-plugin=${ZERO_SPEC_LIB_DIR}/libRemoveInstrumentations.so ${prefix}.2.bc -o ${prefix}.2.bc" >> Makefile.bc.tmp
	echo -e "\tclang++ -c ${prefix}.2.bc -o ${prefix}.o -O3 -fno-vectorize -fno-trapping-math -fno-math-errno" >> Makefile.bc.tmp
	# rm ${prefix}.2.bc
done
echo -e "\n" >> Makefile.bcopt
cat Makefile.bc.tmp >> Makefile.bcopt
rm Makefile.bc.tmp
