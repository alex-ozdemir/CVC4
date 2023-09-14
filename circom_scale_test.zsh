#!/usr/bin/env zsh
set -e

script_dir=${0:a:h}
circom_template_path=$1
[[ -a $circom_template_path ]] || (echo "missing $circom_template_path" && exit 2)
lo=$2
hi=$3
circom_param=8
shift
for i in $@
do
    echo param: $i
    circom_path=${circom_template_path:r}_$i.circom
    cat $circom_template_path | sed "s/$circom_param/$i/" > $circom_path
    $script_dir/../Picus/to_smt2.sh $circom_path > /dev/null
    smt2_path=${circom_template_path:t:r}_$i.smt2
    [[ -a $smt2_path ]] || (echo no smt2 $smt2_path && exit 2)
    # time ./bin/cvc5 $smt2_path --ff-solver int --dump-models --check-models
    time ./bin/cvc5 $smt2_path --ff-solver split -t ffl -t ffl::bitprop -t ffl::gb --ff-bitsum -t ff::bitsum |& tee out$i
    # time ./bin/cvc5 $smt2_path --ff-solver split -t ffl --ff-bitsum
    # time ./bin/cvc5 $smt2_path --ff-solver gb
    rm $circom_path
    #rm $smt2_path
done
