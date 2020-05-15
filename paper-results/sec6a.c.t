__main__:102:INFO (<module>) - Dynamite's logger_level: DEBUG
__main__:103:INFO (<module>) - Dig's logger_level: WARNING
__main__:104:INFO (<module>) - Timeout: 300s
__main__:106:INFO (<module>) - 2020-05-15 13:26:07.472433: dynamo.py ../benchmarks/paper/sec6a.c -t
/home/exp/tools/SageMath/local/lib/python3.7/site-packages/pyximport/pyximport.py:51: DeprecationWarning: the imp module is deprecated in favour of importlib; see the module's documentation for alternative uses
  import imp
analysis:72:DEBUG (__init__) - Create C source for mainQ: /var/tmp/Dig_vg2xsbg9
analysis:80:DEBUG (__init__) - trans_cmd: /home/exp/eric/dynamo/deps/dynamo-instr/src/cil/bin/cilly --save-temps -D HAPPY_MOOD --dotransform /home/exp/eric/dynamo/benchmarks/paper/sec6a.c --out=/var/tmp/Dig_vg2xsbg9/sec6a.c --bnd=500
analysis:87:DEBUG (__init__) - cg: defaultdict(<class 'list'>, {'vloop_12': ['exit'], 'mainQ': ['vloop_12'], 'main': ['mainQ']})
analysis:98:DEBUG (__init__) - postorder_vloop_ids: ['vloop_12']
analysis:107:DEBUG (__init__) - inp_decls (<class 'data.prog.Symbs'>): I x, I y
analysis:108:DEBUG (__init__) - inv_decls (<class 'data.prog.DSymbs'>): {'vtrace1_12': (Symb(name='x', typ='I'), Symb(name='y', typ='I')), 'vtrace2_12': (Symb(name='x', typ='I'), Symb(name='y', typ='I')), 'vtrace3_12': (Symb(name='x', typ='I'), Symb(name='y', typ='I'))}
__main__:152:DEBUG (<module>) - prove_process: 14716
lib:43:DEBUG (gen_rand_inps) - gen 107/100 random inps
utils.profiling:31:DEBUG (timed) - gen_rand_inps: 120.18ms
lib:54:DEBUG (get_traces_from_inps) - inp_decls: I x, I y
lib:55:DEBUG (get_traces_from_inps) - inv_decls: {'vtrace1_12': (Symb(name='x', typ='I'), Symb(name='y', typ='I')), 'vtrace2_12': (Symb(name='x', typ='I'), Symb(name='y', typ='I')), 'vtrace3_12': (Symb(name='x', typ='I'), Symb(name='y', typ='I'))}
utils.profiling:31:DEBUG (timed) - _get_traces_mp: 143.53ms
utils.profiling:31:DEBUG (timed) - _merge_traces: 133.62ms
utils.profiling:31:DEBUG (timed) - get_traces_from_inps: 277.72ms
analysis:1101:DEBUG (prove) - itraces: 107
analysis:1107:DEBUG (prove) - Analysing Termination vloop_12
analysis:1046:DEBUG (prove_term_vloop) - classify_inps: vloop_12
analysis:1049:DEBUG (prove_term_vloop) - itraces: 107
lib:208:DEBUG (print_inps) - x=-26,y=-28: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=-272,y=-20: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=14,y=-4: [('vtrace1_12', 1), ('vtrace2_12', 4), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=-8,y=15: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=299,y=-6: [('vtrace1_12', 1), ('vtrace2_12', 50), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=-285,y=-2: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=12,y=3: [('vtrace1_12', 1), ('vtrace2_12', 500)]
lib:208:DEBUG (print_inps) - x=-276,y=15: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=-273,y=-272: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=14,y=-279: [('vtrace1_12', 1), ('vtrace2_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=-287,y=15: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=11,y=0: [('vtrace1_12', 1), ('vtrace2_12', 500)]
lib:208:DEBUG (print_inps) - x=281,y=8: [('vtrace1_12', 1), ('vtrace2_12', 500)]
lib:208:DEBUG (print_inps) - x=-30,y=12: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=-13,y=-291: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=25,y=-27: [('vtrace1_12', 1), ('vtrace2_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=-288,y=272: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=274,y=-17: [('vtrace1_12', 1), ('vtrace2_12', 17), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=11,y=290: [('vtrace1_12', 1), ('vtrace2_12', 500)]
lib:208:DEBUG (print_inps) - x=-10,y=275: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=-284,y=-285: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=-25,y=-290: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=278,y=0: [('vtrace1_12', 1), ('vtrace2_12', 500)]
lib:208:DEBUG (print_inps) - x=13,y=299: [('vtrace1_12', 1), ('vtrace2_12', 500)]
lib:208:DEBUG (print_inps) - x=14,y=29: [('vtrace1_12', 1), ('vtrace2_12', 500)]
lib:208:DEBUG (print_inps) - x=284,y=283: [('vtrace1_12', 1), ('vtrace2_12', 500)]
lib:208:DEBUG (print_inps) - x=-296,y=-26: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=10,y=-15: [('vtrace1_12', 1), ('vtrace2_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=12,y=-10: [('vtrace1_12', 1), ('vtrace2_12', 2), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=-14,y=3: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=287,y=-290: [('vtrace1_12', 1), ('vtrace2_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=-290,y=-279: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=-297,y=3: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=-277,y=-1: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=-12,y=-6: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=1,y=274: [('vtrace1_12', 1), ('vtrace2_12', 500)]
lib:208:DEBUG (print_inps) - x=5,y=-291: [('vtrace1_12', 1), ('vtrace2_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=5,y=-5: [('vtrace1_12', 1), ('vtrace2_12', 2), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=11,y=-274: [('vtrace1_12', 1), ('vtrace2_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=13,y=-4: [('vtrace1_12', 1), ('vtrace2_12', 4), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=-30,y=7: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=12,y=-274: [('vtrace1_12', 1), ('vtrace2_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=-16,y=289: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=-17,y=27: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=10,y=-5: [('vtrace1_12', 1), ('vtrace2_12', 3), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=16,y=271: [('vtrace1_12', 1), ('vtrace2_12', 500)]
lib:208:DEBUG (print_inps) - x=0,y=0: [('vtrace1_12', 1), ('vtrace2_12', 500)]
lib:208:DEBUG (print_inps) - x=289,y=-1: [('vtrace1_12', 1), ('vtrace2_12', 290), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=290,y=29: [('vtrace1_12', 1), ('vtrace2_12', 500)]
lib:208:DEBUG (print_inps) - x=272,y=293: [('vtrace1_12', 1), ('vtrace2_12', 500)]
lib:208:DEBUG (print_inps) - x=-10,y=299: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=295,y=8: [('vtrace1_12', 1), ('vtrace2_12', 500)]
lib:208:DEBUG (print_inps) - x=28,y=283: [('vtrace1_12', 1), ('vtrace2_12', 500)]
lib:208:DEBUG (print_inps) - x=-8,y=291: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=-299,y=0: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=10,y=-288: [('vtrace1_12', 1), ('vtrace2_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=6,y=-11: [('vtrace1_12', 1), ('vtrace2_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=-16,y=14: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=294,y=-9: [('vtrace1_12', 1), ('vtrace2_12', 33), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=8,y=-21: [('vtrace1_12', 1), ('vtrace2_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=-16,y=8: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=14,y=5: [('vtrace1_12', 1), ('vtrace2_12', 500)]
lib:208:DEBUG (print_inps) - x=-275,y=-16: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=-2,y=-15: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=-14,y=-8: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=22,y=-2: [('vtrace1_12', 1), ('vtrace2_12', 12), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=5,y=3: [('vtrace1_12', 1), ('vtrace2_12', 500)]
lib:208:DEBUG (print_inps) - x=289,y=12: [('vtrace1_12', 1), ('vtrace2_12', 500)]
lib:208:DEBUG (print_inps) - x=284,y=-300: [('vtrace1_12', 1), ('vtrace2_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=19,y=8: [('vtrace1_12', 1), ('vtrace2_12', 500)]
lib:208:DEBUG (print_inps) - x=-5,y=286: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=5,y=2: [('vtrace1_12', 1), ('vtrace2_12', 500)]
lib:208:DEBUG (print_inps) - x=-8,y=-2: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=-294,y=8: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=15,y=-286: [('vtrace1_12', 1), ('vtrace2_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=-15,y=-18: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=290,y=-14: [('vtrace1_12', 1), ('vtrace2_12', 21), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=-1,y=-282: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=-3,y=2: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=-9,y=10: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=-15,y=27: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=290,y=288: [('vtrace1_12', 1), ('vtrace2_12', 500)]
lib:208:DEBUG (print_inps) - x=-9,y=-287: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=-13,y=-8: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=7,y=-23: [('vtrace1_12', 1), ('vtrace2_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=-14,y=-2: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=-3,y=271: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=277,y=21: [('vtrace1_12', 1), ('vtrace2_12', 500)]
lib:208:DEBUG (print_inps) - x=-11,y=-288: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=17,y=13: [('vtrace1_12', 1), ('vtrace2_12', 500)]
lib:208:DEBUG (print_inps) - x=283,y=-11: [('vtrace1_12', 1), ('vtrace2_12', 26), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=23,y=-13: [('vtrace1_12', 1), ('vtrace2_12', 2), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=-291,y=-15: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=10,y=14: [('vtrace1_12', 1), ('vtrace2_12', 500)]
lib:208:DEBUG (print_inps) - x=-21,y=-292: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=7,y=1: [('vtrace1_12', 1), ('vtrace2_12', 500)]
lib:208:DEBUG (print_inps) - x=-3,y=7: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=25,y=1: [('vtrace1_12', 1), ('vtrace2_12', 500)]
lib:208:DEBUG (print_inps) - x=-274,y=295: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=-284,y=290: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=-1,y=-10: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=19,y=294: [('vtrace1_12', 1), ('vtrace2_12', 500)]
lib:208:DEBUG (print_inps) - x=-15,y=-24: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=-13,y=-3: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=-24,y=-14: [('vtrace1_12', 1), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=286,y=-271: [('vtrace1_12', 1), ('vtrace2_12', 2), ('vtrace3_12', 1)]
lib:208:DEBUG (print_inps) - x=-8,y=2: [('vtrace1_12', 1), ('vtrace3_12', 1)]
analysis:1051:DEBUG (prove_term_vloop) - base_term_inps: 53
analysis:1052:DEBUG (prove_term_vloop) - term_inps: 27
analysis:1053:DEBUG (prove_term_vloop) - mayloop_inps: 27
analysis:863:DEBUG (infer_ranking_functions) - vloop: vloop_12
analysis:864:DEBUG (infer_ranking_functions) - term_itraces: 27
analysis:911:DEBUG (infer_ranking_functions) - train_rand_trans: 191
analysis:918:DEBUG (_infer_ranking_functions_from_trans) - rnk_template (<class 'sage.symbolic.expression.Expression'>): uk_1*x + uk_2*y + uk_0
analysis:919:DEBUG (_infer_ranking_functions_from_trans) - uks: [uk_0, uk_1, uk_2]
analysis:943:DEBUG (_infer_ranking_functions_from_trans) - train_term_rand_trans: 191
analysis:950:DEBUG (_infer_ranking_functions_from_trans) - model: [uk_1 = 1, uk_2 = 0, uk_0 = 0]
analysis:954:DEBUG (_infer_ranking_functions_from_trans) - t1: uk_0 + 15*uk_1 + -271*uk_2
analysis:955:DEBUG (_infer_ranking_functions_from_trans) - t2: uk_0 + -256*uk_1 + -271*uk_2
analysis:956:DEBUG (_infer_ranking_functions_from_trans) - rf: x
analysis:985:DEBUG (_infer_ranking_functions_from_trans) - train_term_rand_trans: 0
analysis:986:DEBUG (_infer_ranking_functions_from_trans) - ranking_function_list: [x]
utils.profiling:31:DEBUG (timed) - infer_ranking_functions: 740.66ms
analysis:1067:DEBUG (prove_term_vloop) - validate_ranking_functions: vloop_12
analysis:994:DEBUG (validate_ranking_functions) - ranks_str: x
validate:123:DEBUG (gen_validate_file) - validate_cmd: /home/exp/eric/dynamo/deps/dynamo-instr/src/cil/bin/cilly --save-temps -D HAPPY_MOOD --dovalidate /home/exp/eric/dynamo/benchmarks/paper/sec6a.c --out=/var/tmp/Dig_vg2xsbg9/vloop_12/par/validate/sec6a.c --pos=12 --ranks="x"
validate:41:DEBUG (prove_reach) - pcmd: /home/exp/tools/CPAchecker-1.9-unix/scripts/cpa.sh -spec /home/exp/tools/reachability.prp -predicateAnalysis -setprop counterexample.export.compressWitness=false /var/tmp/Dig_vg2xsbg9/vloop_12/par/validate/sec6a.c
validate:41:DEBUG (prove_reach) - pcmd: /home/exp/tools/ultimate/releaseScripts/default/UAutomizer-linux/Ultimate.py --spec /home/exp/tools/reachability.prp --architecture 32bit --witness-dir /var/tmp/Dig_vg2xsbg9/vloop_12/par/uatm --witness-name witness.graphml --file /var/tmp/Dig_vg2xsbg9/vloop_12/par/validate/sec6a.c
validate:41:DEBUG (prove_reach) - pcmd: /home/exp/tools/ultimate/releaseScripts/default/UTaipan-linux/Ultimate.py --spec /home/exp/tools/reachability.prp --architecture 32bit --witness-dir /var/tmp/Dig_vg2xsbg9/vloop_12/par/utp --witness-name witness.graphml --file /var/tmp/Dig_vg2xsbg9/vloop_12/par/validate/sec6a.c
validate:46:DEBUG (prove_reach) - res: False
validate:61:DEBUG (validate_witness) - vcmd: /home/exp/tools/CPAchecker-1.9-unix/scripts/cpa.sh -spec /home/exp/tools/reachability.prp -witnessValidation -witness /var/tmp/Dig_vg2xsbg9/vloop_12/par/cpa/output/Counterexample.1.graphml /var/tmp/Dig_vg2xsbg9/vloop_12/par/validate/sec6a.c
validate:46:DEBUG (prove_reach) - res: False
validate:61:DEBUG (validate_witness) - vcmd: /home/exp/tools/ultimate/releaseScripts/default/UTaipan-linux/Ultimate.py --spec /home/exp/tools/reachability.prp --architecture 32bit --validate /var/tmp/Dig_vg2xsbg9/vloop_12/par/utp/witness.graphml --file /var/tmp/Dig_vg2xsbg9/vloop_12/par/validate/sec6a.c
validate:46:DEBUG (prove_reach) - res: False
validate:61:DEBUG (validate_witness) - vcmd: /home/exp/tools/ultimate/releaseScripts/default/UAutomizer-linux/Ultimate.py --spec /home/exp/tools/reachability.prp --architecture 32bit --validate /var/tmp/Dig_vg2xsbg9/vloop_12/par/uatm/witness.graphml --file /var/tmp/Dig_vg2xsbg9/vloop_12/par/validate/sec6a.c
validate:49:DEBUG (prove_reach) - validate_witness: DONE
validate:50:DEBUG (prove_reach) - cex: None
validate:253:DEBUG (prove_reach) - wrs: [('cpa', (False, None))]
validate:256:DEBUG (prove_reach) - Got result firstly from cpa
utils.profiling:31:DEBUG (timed) - prove_reach: 3804.63ms
analysis:1007:DEBUG (validate_ranking_functions) - r: False
utils.profiling:31:DEBUG (timed) - validate_ranking_functions: 3944.50ms
analysis:1069:DEBUG (prove_term_vloop) - Termination result (vloop_12): False ([x])
utils.profiling:31:DEBUG (timed) - prove_term_vloop: 4689.88ms
utils.profiling:31:DEBUG (timed) - prove: 5093.54ms
utils.profiling:31:DEBUG (timed) - prove: 5093.91ms
Termination result: None
Time log:
gen_rand_inps: 0.120s
_get_traces_mp: 0.144s
_merge_traces: 0.134s
get_traces_from_inps: 0.278s
infer_ranking_functions: 0.741s
prove_reach: 3.805s
validate_ranking_functions: 3.945s
prove_term_vloop: 4.690s
prove: 5.094s
