(set-info :smt-lib-version 2.6)
(set-logic QF_UF)
(set-info :source |
CADE ATP System competition. See http://www.cs.miami.edu/~tptp/CASC
 for more information. 

This benchmark was obtained by trying to find a finite model of a first-order 
formula (Albert Oliveras).
|)
(set-info :category "crafted")
(set-info :status unsat)
(declare-sort U 0)
(declare-fun c5 () U)
(declare-fun c6 () U)
(declare-fun f3 (U U) U)
(declare-fun f4 (U) U)
(declare-fun f1 (U U) U)
(declare-fun c2 () U)
(declare-fun c_0 () U)
(declare-fun c_1 () U)
(declare-fun c_2 () U)
(declare-fun c_3 () U)
(declare-fun c_4 () U)
(assert (let ((?v_0 (f4 c_0)) (?v_6 (f3 c_0 c_0))) (let ((?v_55 (f4 ?v_6)) (?v_8 (f3 c_0 c_1))) (let ((?v_56 (f4 ?v_8)) (?v_10 (f3 c_0 c_2))) (let ((?v_57 (f4 ?v_10)) (?v_12 (f3 c_0 c_3))) (let ((?v_58 (f4 ?v_12)) (?v_14 (f3 c_0 c_4))) (let ((?v_59 (f4 ?v_14)) (?v_1 (f4 c_1)) (?v_35 (f3 c_1 c_0))) (let ((?v_60 (f4 ?v_35)) (?v_36 (f3 c_1 c_1))) (let ((?v_61 (f4 ?v_36)) (?v_37 (f3 c_1 c_2))) (let ((?v_62 (f4 ?v_37)) (?v_38 (f3 c_1 c_3))) (let ((?v_63 (f4 ?v_38)) (?v_39 (f3 c_1 c_4))) (let ((?v_64 (f4 ?v_39)) (?v_2 (f4 c_2)) (?v_40 (f3 c_2 c_0))) (let ((?v_65 (f4 ?v_40)) (?v_41 (f3 c_2 c_1))) (let ((?v_66 (f4 ?v_41)) (?v_42 (f3 c_2 c_2))) (let ((?v_67 (f4 ?v_42)) (?v_43 (f3 c_2 c_3))) (let ((?v_68 (f4 ?v_43)) (?v_44 (f3 c_2 c_4))) (let ((?v_69 (f4 ?v_44)) (?v_3 (f4 c_3)) (?v_45 (f3 c_3 c_0))) (let ((?v_70 (f4 ?v_45)) (?v_46 (f3 c_3 c_1))) (let ((?v_71 (f4 ?v_46)) (?v_47 (f3 c_3 c_2))) (let ((?v_72 (f4 ?v_47)) (?v_48 (f3 c_3 c_3))) (let ((?v_73 (f4 ?v_48)) (?v_49 (f3 c_3 c_4))) (let ((?v_74 (f4 ?v_49)) (?v_4 (f4 c_4)) (?v_50 (f3 c_4 c_0))) (let ((?v_75 (f4 ?v_50)) (?v_51 (f3 c_4 c_1))) (let ((?v_76 (f4 ?v_51)) (?v_52 (f3 c_4 c_2))) (let ((?v_77 (f4 ?v_52)) (?v_53 (f3 c_4 c_3))) (let ((?v_78 (f4 ?v_53)) (?v_54 (f3 c_4 c_4))) (let ((?v_79 (f4 ?v_54)) (?v_5 (f1 c_0 c_0)) (?v_7 (f1 c_0 c_1)) (?v_9 (f1 c_0 c_2)) (?v_11 (f1 c_0 c_3)) (?v_13 (f1 c_0 c_4)) (?v_15 (f1 c_1 c_0)) (?v_16 (f1 c_1 c_1)) (?v_17 (f1 c_1 c_2)) (?v_18 (f1 c_1 c_3)) (?v_19 (f1 c_1 c_4)) (?v_20 (f1 c_2 c_0)) (?v_21 (f1 c_2 c_1)) (?v_22 (f1 c_2 c_2)) (?v_23 (f1 c_2 c_3)) (?v_24 (f1 c_2 c_4)) (?v_25 (f1 c_3 c_0)) (?v_26 (f1 c_3 c_1)) (?v_27 (f1 c_3 c_2)) (?v_28 (f1 c_3 c_3)) (?v_29 (f1 c_3 c_4)) (?v_30 (f1 c_4 c_0)) (?v_31 (f1 c_4 c_1)) (?v_32 (f1 c_4 c_2)) (?v_33 (f1 c_4 c_3)) (?v_34 (f1 c_4 c_4)) (?v_80 (f1 ?v_6 ?v_6)) (?v_81 (f1 ?v_8 ?v_8)) (?v_82 (f1 ?v_10 ?v_10)) (?v_83 (f1 ?v_12 ?v_12)) (?v_84 (f1 ?v_14 ?v_14)) (?v_85 (f1 ?v_35 ?v_35)) (?v_86 (f1 ?v_36 ?v_36)) (?v_87 (f1 ?v_37 ?v_37)) (?v_88 (f1 ?v_38 ?v_38)) (?v_89 (f1 ?v_39 ?v_39)) (?v_90 (f1 ?v_40 ?v_40)) (?v_91 (f1 ?v_41 ?v_41)) (?v_92 (f1 ?v_42 ?v_42)) (?v_93 (f1 ?v_43 ?v_43)) (?v_94 (f1 ?v_44 ?v_44)) (?v_95 (f1 ?v_45 ?v_45)) (?v_96 (f1 ?v_46 ?v_46)) (?v_97 (f1 ?v_47 ?v_47)) (?v_98 (f1 ?v_48 ?v_48)) (?v_99 (f1 ?v_49 ?v_49)) (?v_100 (f1 ?v_50 ?v_50)) (?v_101 (f1 ?v_51 ?v_51)) (?v_102 (f1 ?v_52 ?v_52)) (?v_103 (f1 ?v_53 ?v_53)) (?v_104 (f1 ?v_54 ?v_54))) (let ((?v_110 (= ?v_5 ?v_5)) (?v_117 (= ?v_16 ?v_16)) (?v_137 (= ?v_22 ?v_22)) (?v_138 (= ?v_28 ?v_28)) (?v_139 (= ?v_34 ?v_34)) (?v_105 (= (f3 ?v_6 c_0) (f3 c_0 ?v_6))) (?v_106 (= (f3 ?v_36 c_1) (f3 c_1 ?v_36))) (?v_107 (= (f3 ?v_42 c_2) (f3 c_2 ?v_42))) (?v_108 (= (f3 ?v_48 c_3) (f3 c_3 ?v_48))) (?v_109 (= (f3 ?v_54 c_4) (f3 c_4 ?v_54)))) (let ((?v_140 (not ?v_110)) (?v_111 (= c_0 c_0)) (?v_112 (= c_0 c_1)) (?v_113 (= c_0 c_2)) (?v_114 (= c_0 c_3)) (?v_115 (= c_0 c_4)) (?v_116 (= c_1 c_0)) (?v_141 (not (= ?v_7 ?v_7))) (?v_118 (= c_1 c_1)) (?v_119 (= c_1 c_2)) (?v_120 (= c_1 c_3)) (?v_121 (= c_1 c_4)) (?v_122 (= c_2 c_0)) (?v_123 (= c_2 c_1)) (?v_142 (not (= ?v_9 ?v_9))) (?v_124 (= c_2 c_2)) (?v_125 (= c_2 c_3)) (?v_126 (= c_2 c_4)) (?v_127 (= c_3 c_0)) (?v_128 (= c_3 c_1)) (?v_129 (= c_3 c_2)) (?v_143 (not (= ?v_11 ?v_11))) (?v_130 (= c_3 c_3)) (?v_131 (= c_3 c_4)) (?v_132 (= c_4 c_0)) (?v_133 (= c_4 c_1)) (?v_134 (= c_4 c_2)) (?v_135 (= c_4 c_3)) (?v_144 (not (= ?v_13 ?v_13))) (?v_136 (= c_4 c_4)) (?v_145 (not (= ?v_15 ?v_15))) (?v_146 (not ?v_117)) (?v_147 (not (= ?v_17 ?v_17))) (?v_148 (not (= ?v_18 ?v_18))) (?v_149 (not (= ?v_19 ?v_19))) (?v_150 (not (= ?v_20 ?v_20))) (?v_151 (not (= ?v_21 ?v_21))) (?v_152 (not ?v_137)) (?v_153 (not (= ?v_23 ?v_23))) (?v_154 (not (= ?v_24 ?v_24))) (?v_155 (not (= ?v_25 ?v_25))) (?v_156 (not (= ?v_26 ?v_26))) (?v_157 (not (= ?v_27 ?v_27))) (?v_158 (not ?v_138)) (?v_159 (not (= ?v_29 ?v_29))) (?v_160 (not (= ?v_30 ?v_30))) (?v_161 (not (= ?v_31 ?v_31))) (?v_162 (not (= ?v_32 ?v_32))) (?v_163 (not (= ?v_33 ?v_33))) (?v_164 (not ?v_139))) (and (distinct c_0 c_1 c_2 c_3 c_4) (not (= (f3 (f3 c5 c6) c5) (f3 c5 (f3 c6 c5)))) (= (f3 ?v_0 c_0) ?v_55) (= (f3 ?v_0 c_1) ?v_56) (= (f3 ?v_0 c_2) ?v_57) (= (f3 ?v_0 c_3) ?v_58) (= (f3 ?v_0 c_4) ?v_59) (= (f3 ?v_1 c_0) ?v_60) (= (f3 ?v_1 c_1) ?v_61) (= (f3 ?v_1 c_2) ?v_62) (= (f3 ?v_1 c_3) ?v_63) (= (f3 ?v_1 c_4) ?v_64) (= (f3 ?v_2 c_0) ?v_65) (= (f3 ?v_2 c_1) ?v_66) (= (f3 ?v_2 c_2) ?v_67) (= (f3 ?v_2 c_3) ?v_68) (= (f3 ?v_2 c_4) ?v_69) (= (f3 ?v_3 c_0) ?v_70) (= (f3 ?v_3 c_1) ?v_71) (= (f3 ?v_3 c_2) ?v_72) (= (f3 ?v_3 c_3) ?v_73) (= (f3 ?v_3 c_4) ?v_74) (= (f3 ?v_4 c_0) ?v_75) (= (f3 ?v_4 c_1) ?v_76) (= (f3 ?v_4 c_2) ?v_77) (= (f3 ?v_4 c_3) ?v_78) (= (f3 ?v_4 c_4) ?v_79) (= (f4 ?v_5) (f1 ?v_0 ?v_0)) (= (f4 ?v_7) (f1 ?v_0 ?v_1)) (= (f4 ?v_9) (f1 ?v_0 ?v_2)) (= (f4 ?v_11) (f1 ?v_0 ?v_3)) (= (f4 ?v_13) (f1 ?v_0 ?v_4)) (= (f4 ?v_15) (f1 ?v_1 ?v_0)) (= (f4 ?v_16) (f1 ?v_1 ?v_1)) (= (f4 ?v_17) (f1 ?v_1 ?v_2)) (= (f4 ?v_18) (f1 ?v_1 ?v_3)) (= (f4 ?v_19) (f1 ?v_1 ?v_4)) (= (f4 ?v_20) (f1 ?v_2 ?v_0)) (= (f4 ?v_21) (f1 ?v_2 ?v_1)) (= (f4 ?v_22) (f1 ?v_2 ?v_2)) (= (f4 ?v_23) (f1 ?v_2 ?v_3)) (= (f4 ?v_24) (f1 ?v_2 ?v_4)) (= (f4 ?v_25) (f1 ?v_3 ?v_0)) (= (f4 ?v_26) (f1 ?v_3 ?v_1)) (= (f4 ?v_27) (f1 ?v_3 ?v_2)) (= (f4 ?v_28) (f1 ?v_3 ?v_3)) (= (f4 ?v_29) (f1 ?v_3 ?v_4)) (= (f4 ?v_30) (f1 ?v_4 ?v_0)) (= (f4 ?v_31) (f1 ?v_4 ?v_1)) (= (f4 ?v_32) (f1 ?v_4 ?v_2)) (= (f4 ?v_33) (f1 ?v_4 ?v_3)) (= (f4 ?v_34) (f1 ?v_4 ?v_4)) (= (f3 c_0 ?v_5) ?v_80) (= (f3 c_0 ?v_7) (f1 ?v_6 ?v_8)) (= (f3 c_0 ?v_9) (f1 ?v_6 ?v_10)) (= (f3 c_0 ?v_11) (f1 ?v_6 ?v_12)) (= (f3 c_0 ?v_13) (f1 ?v_6 ?v_14)) (= (f3 c_0 ?v_15) (f1 ?v_8 ?v_6)) (= (f3 c_0 ?v_16) ?v_81) (= (f3 c_0 ?v_17) (f1 ?v_8 ?v_10)) (= (f3 c_0 ?v_18) (f1 ?v_8 ?v_12)) (= (f3 c_0 ?v_19) (f1 ?v_8 ?v_14)) (= (f3 c_0 ?v_20) (f1 ?v_10 ?v_6)) (= (f3 c_0 ?v_21) (f1 ?v_10 ?v_8)) (= (f3 c_0 ?v_22) ?v_82) (= (f3 c_0 ?v_23) (f1 ?v_10 ?v_12)) (= (f3 c_0 ?v_24) (f1 ?v_10 ?v_14)) (= (f3 c_0 ?v_25) (f1 ?v_12 ?v_6)) (= (f3 c_0 ?v_26) (f1 ?v_12 ?v_8)) (= (f3 c_0 ?v_27) (f1 ?v_12 ?v_10)) (= (f3 c_0 ?v_28) ?v_83) (= (f3 c_0 ?v_29) (f1 ?v_12 ?v_14)) (= (f3 c_0 ?v_30) (f1 ?v_14 ?v_6)) (= (f3 c_0 ?v_31) (f1 ?v_14 ?v_8)) (= (f3 c_0 ?v_32) (f1 ?v_14 ?v_10)) (= (f3 c_0 ?v_33) (f1 ?v_14 ?v_12)) (= (f3 c_0 ?v_34) ?v_84) (= (f3 c_1 ?v_5) ?v_85) (= (f3 c_1 ?v_7) (f1 ?v_35 ?v_36)) (= (f3 c_1 ?v_9) (f1 ?v_35 ?v_37)) (= (f3 c_1 ?v_11) (f1 ?v_35 ?v_38)) (= (f3 c_1 ?v_13) (f1 ?v_35 ?v_39)) (= (f3 c_1 ?v_15) (f1 ?v_36 ?v_35)) (= (f3 c_1 ?v_16) ?v_86) (= (f3 c_1 ?v_17) (f1 ?v_36 ?v_37)) (= (f3 c_1 ?v_18) (f1 ?v_36 ?v_38)) (= (f3 c_1 ?v_19) (f1 ?v_36 ?v_39)) (= (f3 c_1 ?v_20) (f1 ?v_37 ?v_35)) (= (f3 c_1 ?v_21) (f1 ?v_37 ?v_36)) (= (f3 c_1 ?v_22) ?v_87) (= (f3 c_1 ?v_23) (f1 ?v_37 ?v_38)) (= (f3 c_1 ?v_24) (f1 ?v_37 ?v_39)) (= (f3 c_1 ?v_25) (f1 ?v_38 ?v_35)) (= (f3 c_1 ?v_26) (f1 ?v_38 ?v_36)) (= (f3 c_1 ?v_27) (f1 ?v_38 ?v_37)) (= (f3 c_1 ?v_28) ?v_88) (= (f3 c_1 ?v_29) (f1 ?v_38 ?v_39)) (= (f3 c_1 ?v_30) (f1 ?v_39 ?v_35)) (= (f3 c_1 ?v_31) (f1 ?v_39 ?v_36)) (= (f3 c_1 ?v_32) (f1 ?v_39 ?v_37)) (= (f3 c_1 ?v_33) (f1 ?v_39 ?v_38)) (= (f3 c_1 ?v_34) ?v_89) (= (f3 c_2 ?v_5) ?v_90) (= (f3 c_2 ?v_7) (f1 ?v_40 ?v_41)) (= (f3 c_2 ?v_9) (f1 ?v_40 ?v_42)) (= (f3 c_2 ?v_11) (f1 ?v_40 ?v_43)) (= (f3 c_2 ?v_13) (f1 ?v_40 ?v_44)) (= (f3 c_2 ?v_15) (f1 ?v_41 ?v_40)) (= (f3 c_2 ?v_16) ?v_91) (= (f3 c_2 ?v_17) (f1 ?v_41 ?v_42)) (= (f3 c_2 ?v_18) (f1 ?v_41 ?v_43)) (= (f3 c_2 ?v_19) (f1 ?v_41 ?v_44)) (= (f3 c_2 ?v_20) (f1 ?v_42 ?v_40)) (= (f3 c_2 ?v_21) (f1 ?v_42 ?v_41)) (= (f3 c_2 ?v_22) ?v_92) (= (f3 c_2 ?v_23) (f1 ?v_42 ?v_43)) (= (f3 c_2 ?v_24) (f1 ?v_42 ?v_44)) (= (f3 c_2 ?v_25) (f1 ?v_43 ?v_40)) (= (f3 c_2 ?v_26) (f1 ?v_43 ?v_41)) (= (f3 c_2 ?v_27) (f1 ?v_43 ?v_42)) (= (f3 c_2 ?v_28) ?v_93) (= (f3 c_2 ?v_29) (f1 ?v_43 ?v_44)) (= (f3 c_2 ?v_30) (f1 ?v_44 ?v_40)) (= (f3 c_2 ?v_31) (f1 ?v_44 ?v_41)) (= (f3 c_2 ?v_32) (f1 ?v_44 ?v_42)) (= (f3 c_2 ?v_33) (f1 ?v_44 ?v_43)) (= (f3 c_2 ?v_34) ?v_94) (= (f3 c_3 ?v_5) ?v_95) (= (f3 c_3 ?v_7) (f1 ?v_45 ?v_46)) (= (f3 c_3 ?v_9) (f1 ?v_45 ?v_47)) (= (f3 c_3 ?v_11) (f1 ?v_45 ?v_48)) (= (f3 c_3 ?v_13) (f1 ?v_45 ?v_49)) (= (f3 c_3 ?v_15) (f1 ?v_46 ?v_45)) (= (f3 c_3 ?v_16) ?v_96) (= (f3 c_3 ?v_17) (f1 ?v_46 ?v_47)) (= (f3 c_3 ?v_18) (f1 ?v_46 ?v_48)) (= (f3 c_3 ?v_19) (f1 ?v_46 ?v_49)) (= (f3 c_3 ?v_20) (f1 ?v_47 ?v_45)) (= (f3 c_3 ?v_21) (f1 ?v_47 ?v_46)) (= (f3 c_3 ?v_22) ?v_97) (= (f3 c_3 ?v_23) (f1 ?v_47 ?v_48)) (= (f3 c_3 ?v_24) (f1 ?v_47 ?v_49)) (= (f3 c_3 ?v_25) (f1 ?v_48 ?v_45)) (= (f3 c_3 ?v_26) (f1 ?v_48 ?v_46)) (= (f3 c_3 ?v_27) (f1 ?v_48 ?v_47)) (= (f3 c_3 ?v_28) ?v_98) (= (f3 c_3 ?v_29) (f1 ?v_48 ?v_49)) (= (f3 c_3 ?v_30) (f1 ?v_49 ?v_45)) (= (f3 c_3 ?v_31) (f1 ?v_49 ?v_46)) (= (f3 c_3 ?v_32) (f1 ?v_49 ?v_47)) (= (f3 c_3 ?v_33) (f1 ?v_49 ?v_48)) (= (f3 c_3 ?v_34) ?v_99) (= (f3 c_4 ?v_5) ?v_100) (= (f3 c_4 ?v_7) (f1 ?v_50 ?v_51)) (= (f3 c_4 ?v_9) (f1 ?v_50 ?v_52)) (= (f3 c_4 ?v_11) (f1 ?v_50 ?v_53)) (= (f3 c_4 ?v_13) (f1 ?v_50 ?v_54)) (= (f3 c_4 ?v_15) (f1 ?v_51 ?v_50)) (= (f3 c_4 ?v_16) ?v_101) (= (f3 c_4 ?v_17) (f1 ?v_51 ?v_52)) (= (f3 c_4 ?v_18) (f1 ?v_51 ?v_53)) (= (f3 c_4 ?v_19) (f1 ?v_51 ?v_54)) (= (f3 c_4 ?v_20) (f1 ?v_52 ?v_50)) (= (f3 c_4 ?v_21) (f1 ?v_52 ?v_51)) (= (f3 c_4 ?v_22) ?v_102) (= (f3 c_4 ?v_23) (f1 ?v_52 ?v_53)) (= (f3 c_4 ?v_24) (f1 ?v_52 ?v_54)) (= (f3 c_4 ?v_25) (f1 ?v_53 ?v_50)) (= (f3 c_4 ?v_26) (f1 ?v_53 ?v_51)) (= (f3 c_4 ?v_27) (f1 ?v_53 ?v_52)) (= (f3 c_4 ?v_28) ?v_103) (= (f3 c_4 ?v_29) (f1 ?v_53 ?v_54)) (= (f3 c_4 ?v_30) (f1 ?v_54 ?v_50)) (= (f3 c_4 ?v_31) (f1 ?v_54 ?v_51)) (= (f3 c_4 ?v_32) (f1 ?v_54 ?v_52)) (= (f3 c_4 ?v_33) (f1 ?v_54 ?v_53)) (= (f3 c_4 ?v_34) ?v_104) (= (f3 c_0 ?v_0) ?v_55) (= (f3 c_0 ?v_1) ?v_56) (= (f3 c_0 ?v_2) ?v_57) (= (f3 c_0 ?v_3) ?v_58) (= (f3 c_0 ?v_4) ?v_59) (= (f3 c_1 ?v_0) ?v_60) (= (f3 c_1 ?v_1) ?v_61) (= (f3 c_1 ?v_2) ?v_62) (= (f3 c_1 ?v_3) ?v_63) (= (f3 c_1 ?v_4) ?v_64) (= (f3 c_2 ?v_0) ?v_65) (= (f3 c_2 ?v_1) ?v_66) (= (f3 c_2 ?v_2) ?v_67) (= (f3 c_2 ?v_3) ?v_68) (= (f3 c_2 ?v_4) ?v_69) (= (f3 c_3 ?v_0) ?v_70) (= (f3 c_3 ?v_1) ?v_71) (= (f3 c_3 ?v_2) ?v_72) (= (f3 c_3 ?v_3) ?v_73) (= (f3 c_3 ?v_4) ?v_74) (= (f3 c_4 ?v_0) ?v_75) (= (f3 c_4 ?v_1) ?v_76) (= (f3 c_4 ?v_2) ?v_77) (= (f3 c_4 ?v_3) ?v_78) (= (f3 c_4 ?v_4) ?v_79) ?v_110 (= ?v_7 ?v_15) (= ?v_9 ?v_20) (= ?v_11 ?v_25) (= ?v_13 ?v_30) (= ?v_15 ?v_7) ?v_117 (= ?v_17 ?v_21) (= ?v_18 ?v_26) (= ?v_19 ?v_31) (= ?v_20 ?v_9) (= ?v_21 ?v_17) ?v_137 (= ?v_23 ?v_27) (= ?v_24 ?v_32) (= ?v_25 ?v_11) (= ?v_26 ?v_18) (= ?v_27 ?v_23) ?v_138 (= ?v_29 ?v_33) (= ?v_30 ?v_13) (= ?v_31 ?v_19) (= ?v_32 ?v_24) (= ?v_33 ?v_29) ?v_139 (= (f4 c2) c2) (= (f3 c2 c_0) c2) (= (f3 c2 c_1) c2) (= (f3 c2 c_2) c2) (= (f3 c2 c_3) c2) (= (f3 c2 c_4) c2) ?v_105 (= (f3 ?v_8 c_1) (f3 c_0 ?v_36)) (= (f3 ?v_10 c_2) (f3 c_0 ?v_42)) (= (f3 ?v_12 c_3) (f3 c_0 ?v_48)) (= (f3 ?v_14 c_4) (f3 c_0 ?v_54)) (= (f3 ?v_35 c_0) (f3 c_1 ?v_6)) ?v_106 (= (f3 ?v_37 c_2) (f3 c_1 ?v_42)) (= (f3 ?v_38 c_3) (f3 c_1 ?v_48)) (= (f3 ?v_39 c_4) (f3 c_1 ?v_54)) (= (f3 ?v_40 c_0) (f3 c_2 ?v_6)) (= (f3 ?v_41 c_1) (f3 c_2 ?v_36)) ?v_107 (= (f3 ?v_43 c_3) (f3 c_2 ?v_48)) (= (f3 ?v_44 c_4) (f3 c_2 ?v_54)) (= (f3 ?v_45 c_0) (f3 c_3 ?v_6)) (= (f3 ?v_46 c_1) (f3 c_3 ?v_36)) (= (f3 ?v_47 c_2) (f3 c_3 ?v_42)) ?v_108 (= (f3 ?v_49 c_4) (f3 c_3 ?v_54)) (= (f3 ?v_50 c_0) (f3 c_4 ?v_6)) (= (f3 ?v_51 c_1) (f3 c_4 ?v_36)) (= (f3 ?v_52 c_2) (f3 c_4 ?v_42)) (= (f3 ?v_53 c_3) (f3 c_4 ?v_48)) ?v_109 (= (f3 c_0 c2) c2) (= (f3 c_1 c2) c2) (= (f3 c_2 c2) c2) (= (f3 c_3 c2) c2) (= (f3 c_4 c2) c2) (= (f1 ?v_0 c_0) c2) (= (f1 ?v_1 c_1) c2) (= (f1 ?v_2 c_2) c2) (= (f1 ?v_3 c_3) c2) (= (f1 ?v_4 c_4) c2) (= (f3 ?v_5 c_0) ?v_80) (= (f3 ?v_5 c_1) ?v_81) (= (f3 ?v_5 c_2) ?v_82) (= (f3 ?v_5 c_3) ?v_83) (= (f3 ?v_5 c_4) ?v_84) (= (f3 ?v_7 c_0) (f1 ?v_6 ?v_35)) (= (f3 ?v_7 c_1) (f1 ?v_8 ?v_36)) (= (f3 ?v_7 c_2) (f1 ?v_10 ?v_37)) (= (f3 ?v_7 c_3) (f1 ?v_12 ?v_38)) (= (f3 ?v_7 c_4) (f1 ?v_14 ?v_39)) (= (f3 ?v_9 c_0) (f1 ?v_6 ?v_40)) (= (f3 ?v_9 c_1) (f1 ?v_8 ?v_41)) (= (f3 ?v_9 c_2) (f1 ?v_10 ?v_42)) (= (f3 ?v_9 c_3) (f1 ?v_12 ?v_43)) (= (f3 ?v_9 c_4) (f1 ?v_14 ?v_44)) (= (f3 ?v_11 c_0) (f1 ?v_6 ?v_45)) (= (f3 ?v_11 c_1) (f1 ?v_8 ?v_46)) (= (f3 ?v_11 c_2) (f1 ?v_10 ?v_47)) (= (f3 ?v_11 c_3) (f1 ?v_12 ?v_48)) (= (f3 ?v_11 c_4) (f1 ?v_14 ?v_49)) (= (f3 ?v_13 c_0) (f1 ?v_6 ?v_50)) (= (f3 ?v_13 c_1) (f1 ?v_8 ?v_51)) (= (f3 ?v_13 c_2) (f1 ?v_10 ?v_52)) (= (f3 ?v_13 c_3) (f1 ?v_12 ?v_53)) (= (f3 ?v_13 c_4) (f1 ?v_14 ?v_54)) (= (f3 ?v_15 c_0) (f1 ?v_35 ?v_6)) (= (f3 ?v_15 c_1) (f1 ?v_36 ?v_8)) (= (f3 ?v_15 c_2) (f1 ?v_37 ?v_10)) (= (f3 ?v_15 c_3) (f1 ?v_38 ?v_12)) (= (f3 ?v_15 c_4) (f1 ?v_39 ?v_14)) (= (f3 ?v_16 c_0) ?v_85) (= (f3 ?v_16 c_1) ?v_86) (= (f3 ?v_16 c_2) ?v_87) (= (f3 ?v_16 c_3) ?v_88) (= (f3 ?v_16 c_4) ?v_89) (= (f3 ?v_17 c_0) (f1 ?v_35 ?v_40)) (= (f3 ?v_17 c_1) (f1 ?v_36 ?v_41)) (= (f3 ?v_17 c_2) (f1 ?v_37 ?v_42)) (= (f3 ?v_17 c_3) (f1 ?v_38 ?v_43)) (= (f3 ?v_17 c_4) (f1 ?v_39 ?v_44)) (= (f3 ?v_18 c_0) (f1 ?v_35 ?v_45)) (= (f3 ?v_18 c_1) (f1 ?v_36 ?v_46)) (= (f3 ?v_18 c_2) (f1 ?v_37 ?v_47)) (= (f3 ?v_18 c_3) (f1 ?v_38 ?v_48)) (= (f3 ?v_18 c_4) (f1 ?v_39 ?v_49)) (= (f3 ?v_19 c_0) (f1 ?v_35 ?v_50)) (= (f3 ?v_19 c_1) (f1 ?v_36 ?v_51)) (= (f3 ?v_19 c_2) (f1 ?v_37 ?v_52)) (= (f3 ?v_19 c_3) (f1 ?v_38 ?v_53)) (= (f3 ?v_19 c_4) (f1 ?v_39 ?v_54)) (= (f3 ?v_20 c_0) (f1 ?v_40 ?v_6)) (= (f3 ?v_20 c_1) (f1 ?v_41 ?v_8)) (= (f3 ?v_20 c_2) (f1 ?v_42 ?v_10)) (= (f3 ?v_20 c_3) (f1 ?v_43 ?v_12)) (= (f3 ?v_20 c_4) (f1 ?v_44 ?v_14)) (= (f3 ?v_21 c_0) (f1 ?v_40 ?v_35)) (= (f3 ?v_21 c_1) (f1 ?v_41 ?v_36)) (= (f3 ?v_21 c_2) (f1 ?v_42 ?v_37)) (= (f3 ?v_21 c_3) (f1 ?v_43 ?v_38)) (= (f3 ?v_21 c_4) (f1 ?v_44 ?v_39)) (= (f3 ?v_22 c_0) ?v_90) (= (f3 ?v_22 c_1) ?v_91) (= (f3 ?v_22 c_2) ?v_92) (= (f3 ?v_22 c_3) ?v_93) (= (f3 ?v_22 c_4) ?v_94) (= (f3 ?v_23 c_0) (f1 ?v_40 ?v_45)) (= (f3 ?v_23 c_1) (f1 ?v_41 ?v_46)) (= (f3 ?v_23 c_2) (f1 ?v_42 ?v_47)) (= (f3 ?v_23 c_3) (f1 ?v_43 ?v_48)) (= (f3 ?v_23 c_4) (f1 ?v_44 ?v_49)) (= (f3 ?v_24 c_0) (f1 ?v_40 ?v_50)) (= (f3 ?v_24 c_1) (f1 ?v_41 ?v_51)) (= (f3 ?v_24 c_2) (f1 ?v_42 ?v_52)) (= (f3 ?v_24 c_3) (f1 ?v_43 ?v_53)) (= (f3 ?v_24 c_4) (f1 ?v_44 ?v_54)) (= (f3 ?v_25 c_0) (f1 ?v_45 ?v_6)) (= (f3 ?v_25 c_1) (f1 ?v_46 ?v_8)) (= (f3 ?v_25 c_2) (f1 ?v_47 ?v_10)) (= (f3 ?v_25 c_3) (f1 ?v_48 ?v_12)) (= (f3 ?v_25 c_4) (f1 ?v_49 ?v_14)) (= (f3 ?v_26 c_0) (f1 ?v_45 ?v_35)) (= (f3 ?v_26 c_1) (f1 ?v_46 ?v_36)) (= (f3 ?v_26 c_2) (f1 ?v_47 ?v_37)) (= (f3 ?v_26 c_3) (f1 ?v_48 ?v_38)) (= (f3 ?v_26 c_4) (f1 ?v_49 ?v_39)) (= (f3 ?v_27 c_0) (f1 ?v_45 ?v_40)) (= (f3 ?v_27 c_1) (f1 ?v_46 ?v_41)) (= (f3 ?v_27 c_2) (f1 ?v_47 ?v_42)) (= (f3 ?v_27 c_3) (f1 ?v_48 ?v_43)) (= (f3 ?v_27 c_4) (f1 ?v_49 ?v_44)) (= (f3 ?v_28 c_0) ?v_95) (= (f3 ?v_28 c_1) ?v_96) (= (f3 ?v_28 c_2) ?v_97) (= (f3 ?v_28 c_3) ?v_98) (= (f3 ?v_28 c_4) ?v_99) (= (f3 ?v_29 c_0) (f1 ?v_45 ?v_50)) (= (f3 ?v_29 c_1) (f1 ?v_46 ?v_51)) (= (f3 ?v_29 c_2) (f1 ?v_47 ?v_52)) (= (f3 ?v_29 c_3) (f1 ?v_48 ?v_53)) (= (f3 ?v_29 c_4) (f1 ?v_49 ?v_54)) (= (f3 ?v_30 c_0) (f1 ?v_50 ?v_6)) (= (f3 ?v_30 c_1) (f1 ?v_51 ?v_8)) (= (f3 ?v_30 c_2) (f1 ?v_52 ?v_10)) (= (f3 ?v_30 c_3) (f1 ?v_53 ?v_12)) (= (f3 ?v_30 c_4) (f1 ?v_54 ?v_14)) (= (f3 ?v_31 c_0) (f1 ?v_50 ?v_35)) (= (f3 ?v_31 c_1) (f1 ?v_51 ?v_36)) (= (f3 ?v_31 c_2) (f1 ?v_52 ?v_37)) (= (f3 ?v_31 c_3) (f1 ?v_53 ?v_38)) (= (f3 ?v_31 c_4) (f1 ?v_54 ?v_39)) (= (f3 ?v_32 c_0) (f1 ?v_50 ?v_40)) (= (f3 ?v_32 c_1) (f1 ?v_51 ?v_41)) (= (f3 ?v_32 c_2) (f1 ?v_52 ?v_42)) (= (f3 ?v_32 c_3) (f1 ?v_53 ?v_43)) (= (f3 ?v_32 c_4) (f1 ?v_54 ?v_44)) (= (f3 ?v_33 c_0) (f1 ?v_50 ?v_45)) (= (f3 ?v_33 c_1) (f1 ?v_51 ?v_46)) (= (f3 ?v_33 c_2) (f1 ?v_52 ?v_47)) (= (f3 ?v_33 c_3) (f1 ?v_53 ?v_48)) (= (f3 ?v_33 c_4) (f1 ?v_54 ?v_49)) (= (f3 ?v_34 c_0) ?v_100) (= (f3 ?v_34 c_1) ?v_101) (= (f3 ?v_34 c_2) ?v_102) (= (f3 ?v_34 c_3) ?v_103) (= (f3 ?v_34 c_4) ?v_104) ?v_105 (= (f3 ?v_6 c_1) (f3 c_0 ?v_8)) (= (f3 ?v_6 c_2) (f3 c_0 ?v_10)) (= (f3 ?v_6 c_3) (f3 c_0 ?v_12)) (= (f3 ?v_6 c_4) (f3 c_0 ?v_14)) (= (f3 ?v_36 c_0) (f3 c_1 ?v_35)) ?v_106 (= (f3 ?v_36 c_2) (f3 c_1 ?v_37)) (= (f3 ?v_36 c_3) (f3 c_1 ?v_38)) (= (f3 ?v_36 c_4) (f3 c_1 ?v_39)) (= (f3 ?v_42 c_0) (f3 c_2 ?v_40)) (= (f3 ?v_42 c_1) (f3 c_2 ?v_41)) ?v_107 (= (f3 ?v_42 c_3) (f3 c_2 ?v_43)) (= (f3 ?v_42 c_4) (f3 c_2 ?v_44)) (= (f3 ?v_48 c_0) (f3 c_3 ?v_45)) (= (f3 ?v_48 c_1) (f3 c_3 ?v_46)) (= (f3 ?v_48 c_2) (f3 c_3 ?v_47)) ?v_108 (= (f3 ?v_48 c_4) (f3 c_3 ?v_49)) (= (f3 ?v_54 c_0) (f3 c_4 ?v_50)) (= (f3 ?v_54 c_1) (f3 c_4 ?v_51)) (= (f3 ?v_54 c_2) (f3 c_4 ?v_52)) (= (f3 ?v_54 c_3) (f3 c_4 ?v_53)) ?v_109 (or ?v_140 ?v_111) (or (not (= ?v_5 ?v_7)) ?v_112) (or (not (= ?v_5 ?v_9)) ?v_113) (or (not (= ?v_5 ?v_11)) ?v_114) (or (not (= ?v_5 ?v_13)) ?v_115) (or (not (= ?v_7 ?v_5)) ?v_116) (or ?v_141 ?v_118) (or (not (= ?v_7 ?v_9)) ?v_119) (or (not (= ?v_7 ?v_11)) ?v_120) (or (not (= ?v_7 ?v_13)) ?v_121) (or (not (= ?v_9 ?v_5)) ?v_122) (or (not (= ?v_9 ?v_7)) ?v_123) (or ?v_142 ?v_124) (or (not (= ?v_9 ?v_11)) ?v_125) (or (not (= ?v_9 ?v_13)) ?v_126) (or (not (= ?v_11 ?v_5)) ?v_127) (or (not (= ?v_11 ?v_7)) ?v_128) (or (not (= ?v_11 ?v_9)) ?v_129) (or ?v_143 ?v_130) (or (not (= ?v_11 ?v_13)) ?v_131) (or (not (= ?v_13 ?v_5)) ?v_132) (or (not (= ?v_13 ?v_7)) ?v_133) (or (not (= ?v_13 ?v_9)) ?v_134) (or (not (= ?v_13 ?v_11)) ?v_135) (or ?v_144 ?v_136) (or ?v_145 ?v_111) (or (not (= ?v_15 ?v_16)) ?v_112) (or (not (= ?v_15 ?v_17)) ?v_113) (or (not (= ?v_15 ?v_18)) ?v_114) (or (not (= ?v_15 ?v_19)) ?v_115) (or (not (= ?v_16 ?v_15)) ?v_116) (or ?v_146 ?v_118) (or (not (= ?v_16 ?v_17)) ?v_119) (or (not (= ?v_16 ?v_18)) ?v_120) (or (not (= ?v_16 ?v_19)) ?v_121) (or (not (= ?v_17 ?v_15)) ?v_122) (or (not (= ?v_17 ?v_16)) ?v_123) (or ?v_147 ?v_124) (or (not (= ?v_17 ?v_18)) ?v_125) (or (not (= ?v_17 ?v_19)) ?v_126) (or (not (= ?v_18 ?v_15)) ?v_127) (or (not (= ?v_18 ?v_16)) ?v_128) (or (not (= ?v_18 ?v_17)) ?v_129) (or ?v_148 ?v_130) (or (not (= ?v_18 ?v_19)) ?v_131) (or (not (= ?v_19 ?v_15)) ?v_132) (or (not (= ?v_19 ?v_16)) ?v_133) (or (not (= ?v_19 ?v_17)) ?v_134) (or (not (= ?v_19 ?v_18)) ?v_135) (or ?v_149 ?v_136) (or ?v_150 ?v_111) (or (not (= ?v_20 ?v_21)) ?v_112) (or (not (= ?v_20 ?v_22)) ?v_113) (or (not (= ?v_20 ?v_23)) ?v_114) (or (not (= ?v_20 ?v_24)) ?v_115) (or (not (= ?v_21 ?v_20)) ?v_116) (or ?v_151 ?v_118) (or (not (= ?v_21 ?v_22)) ?v_119) (or (not (= ?v_21 ?v_23)) ?v_120) (or (not (= ?v_21 ?v_24)) ?v_121) (or (not (= ?v_22 ?v_20)) ?v_122) (or (not (= ?v_22 ?v_21)) ?v_123) (or ?v_152 ?v_124) (or (not (= ?v_22 ?v_23)) ?v_125) (or (not (= ?v_22 ?v_24)) ?v_126) (or (not (= ?v_23 ?v_20)) ?v_127) (or (not (= ?v_23 ?v_21)) ?v_128) (or (not (= ?v_23 ?v_22)) ?v_129) (or ?v_153 ?v_130) (or (not (= ?v_23 ?v_24)) ?v_131) (or (not (= ?v_24 ?v_20)) ?v_132) (or (not (= ?v_24 ?v_21)) ?v_133) (or (not (= ?v_24 ?v_22)) ?v_134) (or (not (= ?v_24 ?v_23)) ?v_135) (or ?v_154 ?v_136) (or ?v_155 ?v_111) (or (not (= ?v_25 ?v_26)) ?v_112) (or (not (= ?v_25 ?v_27)) ?v_113) (or (not (= ?v_25 ?v_28)) ?v_114) (or (not (= ?v_25 ?v_29)) ?v_115) (or (not (= ?v_26 ?v_25)) ?v_116) (or ?v_156 ?v_118) (or (not (= ?v_26 ?v_27)) ?v_119) (or (not (= ?v_26 ?v_28)) ?v_120) (or (not (= ?v_26 ?v_29)) ?v_121) (or (not (= ?v_27 ?v_25)) ?v_122) (or (not (= ?v_27 ?v_26)) ?v_123) (or ?v_157 ?v_124) (or (not (= ?v_27 ?v_28)) ?v_125) (or (not (= ?v_27 ?v_29)) ?v_126) (or (not (= ?v_28 ?v_25)) ?v_127) (or (not (= ?v_28 ?v_26)) ?v_128) (or (not (= ?v_28 ?v_27)) ?v_129) (or ?v_158 ?v_130) (or (not (= ?v_28 ?v_29)) ?v_131) (or (not (= ?v_29 ?v_25)) ?v_132) (or (not (= ?v_29 ?v_26)) ?v_133) (or (not (= ?v_29 ?v_27)) ?v_134) (or (not (= ?v_29 ?v_28)) ?v_135) (or ?v_159 ?v_136) (or ?v_160 ?v_111) (or (not (= ?v_30 ?v_31)) ?v_112) (or (not (= ?v_30 ?v_32)) ?v_113) (or (not (= ?v_30 ?v_33)) ?v_114) (or (not (= ?v_30 ?v_34)) ?v_115) (or (not (= ?v_31 ?v_30)) ?v_116) (or ?v_161 ?v_118) (or (not (= ?v_31 ?v_32)) ?v_119) (or (not (= ?v_31 ?v_33)) ?v_120) (or (not (= ?v_31 ?v_34)) ?v_121) (or (not (= ?v_32 ?v_30)) ?v_122) (or (not (= ?v_32 ?v_31)) ?v_123) (or ?v_162 ?v_124) (or (not (= ?v_32 ?v_33)) ?v_125) (or (not (= ?v_32 ?v_34)) ?v_126) (or (not (= ?v_33 ?v_30)) ?v_127) (or (not (= ?v_33 ?v_31)) ?v_128) (or (not (= ?v_33 ?v_32)) ?v_129) (or ?v_163 ?v_130) (or (not (= ?v_33 ?v_34)) ?v_131) (or (not (= ?v_34 ?v_30)) ?v_132) (or (not (= ?v_34 ?v_31)) ?v_133) (or (not (= ?v_34 ?v_32)) ?v_134) (or (not (= ?v_34 ?v_33)) ?v_135) (or ?v_164 ?v_136) (= (f4 ?v_0) c_0) (= (f4 ?v_1) c_1) (= (f4 ?v_2) c_2) (= (f4 ?v_3) c_3) (= (f4 ?v_4) c_4) (= (f1 c2 c_0) c_0) (= (f1 c2 c_1) c_1) (= (f1 c2 c_2) c_2) (= (f1 c2 c_3) c_3) (= (f1 c2 c_4) c_4) (= (f1 c_0 ?v_5) (f1 ?v_5 c_0)) (= (f1 c_0 ?v_7) (f1 ?v_5 c_1)) (= (f1 c_0 ?v_9) (f1 ?v_5 c_2)) (= (f1 c_0 ?v_11) (f1 ?v_5 c_3)) (= (f1 c_0 ?v_13) (f1 ?v_5 c_4)) (= (f1 c_0 ?v_15) (f1 ?v_7 c_0)) (= (f1 c_0 ?v_16) (f1 ?v_7 c_1)) (= (f1 c_0 ?v_17) (f1 ?v_7 c_2)) (= (f1 c_0 ?v_18) (f1 ?v_7 c_3)) (= (f1 c_0 ?v_19) (f1 ?v_7 c_4)) (= (f1 c_0 ?v_20) (f1 ?v_9 c_0)) (= (f1 c_0 ?v_21) (f1 ?v_9 c_1)) (= (f1 c_0 ?v_22) (f1 ?v_9 c_2)) (= (f1 c_0 ?v_23) (f1 ?v_9 c_3)) (= (f1 c_0 ?v_24) (f1 ?v_9 c_4)) (= (f1 c_0 ?v_25) (f1 ?v_11 c_0)) (= (f1 c_0 ?v_26) (f1 ?v_11 c_1)) (= (f1 c_0 ?v_27) (f1 ?v_11 c_2)) (= (f1 c_0 ?v_28) (f1 ?v_11 c_3)) (= (f1 c_0 ?v_29) (f1 ?v_11 c_4)) (= (f1 c_0 ?v_30) (f1 ?v_13 c_0)) (= (f1 c_0 ?v_31) (f1 ?v_13 c_1)) (= (f1 c_0 ?v_32) (f1 ?v_13 c_2)) (= (f1 c_0 ?v_33) (f1 ?v_13 c_3)) (= (f1 c_0 ?v_34) (f1 ?v_13 c_4)) (= (f1 c_1 ?v_5) (f1 ?v_15 c_0)) (= (f1 c_1 ?v_7) (f1 ?v_15 c_1)) (= (f1 c_1 ?v_9) (f1 ?v_15 c_2)) (= (f1 c_1 ?v_11) (f1 ?v_15 c_3)) (= (f1 c_1 ?v_13) (f1 ?v_15 c_4)) (= (f1 c_1 ?v_15) (f1 ?v_16 c_0)) (= (f1 c_1 ?v_16) (f1 ?v_16 c_1)) (= (f1 c_1 ?v_17) (f1 ?v_16 c_2)) (= (f1 c_1 ?v_18) (f1 ?v_16 c_3)) (= (f1 c_1 ?v_19) (f1 ?v_16 c_4)) (= (f1 c_1 ?v_20) (f1 ?v_17 c_0)) (= (f1 c_1 ?v_21) (f1 ?v_17 c_1)) (= (f1 c_1 ?v_22) (f1 ?v_17 c_2)) (= (f1 c_1 ?v_23) (f1 ?v_17 c_3)) (= (f1 c_1 ?v_24) (f1 ?v_17 c_4)) (= (f1 c_1 ?v_25) (f1 ?v_18 c_0)) (= (f1 c_1 ?v_26) (f1 ?v_18 c_1)) (= (f1 c_1 ?v_27) (f1 ?v_18 c_2)) (= (f1 c_1 ?v_28) (f1 ?v_18 c_3)) (= (f1 c_1 ?v_29) (f1 ?v_18 c_4)) (= (f1 c_1 ?v_30) (f1 ?v_19 c_0)) (= (f1 c_1 ?v_31) (f1 ?v_19 c_1)) (= (f1 c_1 ?v_32) (f1 ?v_19 c_2)) (= (f1 c_1 ?v_33) (f1 ?v_19 c_3)) (= (f1 c_1 ?v_34) (f1 ?v_19 c_4)) (= (f1 c_2 ?v_5) (f1 ?v_20 c_0)) (= (f1 c_2 ?v_7) (f1 ?v_20 c_1)) (= (f1 c_2 ?v_9) (f1 ?v_20 c_2)) (= (f1 c_2 ?v_11) (f1 ?v_20 c_3)) (= (f1 c_2 ?v_13) (f1 ?v_20 c_4)) (= (f1 c_2 ?v_15) (f1 ?v_21 c_0)) (= (f1 c_2 ?v_16) (f1 ?v_21 c_1)) (= (f1 c_2 ?v_17) (f1 ?v_21 c_2)) (= (f1 c_2 ?v_18) (f1 ?v_21 c_3)) (= (f1 c_2 ?v_19) (f1 ?v_21 c_4)) (= (f1 c_2 ?v_20) (f1 ?v_22 c_0)) (= (f1 c_2 ?v_21) (f1 ?v_22 c_1)) (= (f1 c_2 ?v_22) (f1 ?v_22 c_2)) (= (f1 c_2 ?v_23) (f1 ?v_22 c_3)) (= (f1 c_2 ?v_24) (f1 ?v_22 c_4)) (= (f1 c_2 ?v_25) (f1 ?v_23 c_0)) (= (f1 c_2 ?v_26) (f1 ?v_23 c_1)) (= (f1 c_2 ?v_27) (f1 ?v_23 c_2)) (= (f1 c_2 ?v_28) (f1 ?v_23 c_3)) (= (f1 c_2 ?v_29) (f1 ?v_23 c_4)) (= (f1 c_2 ?v_30) (f1 ?v_24 c_0)) (= (f1 c_2 ?v_31) (f1 ?v_24 c_1)) (= (f1 c_2 ?v_32) (f1 ?v_24 c_2)) (= (f1 c_2 ?v_33) (f1 ?v_24 c_3)) (= (f1 c_2 ?v_34) (f1 ?v_24 c_4)) (= (f1 c_3 ?v_5) (f1 ?v_25 c_0)) (= (f1 c_3 ?v_7) (f1 ?v_25 c_1)) (= (f1 c_3 ?v_9) (f1 ?v_25 c_2)) (= (f1 c_3 ?v_11) (f1 ?v_25 c_3)) (= (f1 c_3 ?v_13) (f1 ?v_25 c_4)) (= (f1 c_3 ?v_15) (f1 ?v_26 c_0)) (= (f1 c_3 ?v_16) (f1 ?v_26 c_1)) (= (f1 c_3 ?v_17) (f1 ?v_26 c_2)) (= (f1 c_3 ?v_18) (f1 ?v_26 c_3)) (= (f1 c_3 ?v_19) (f1 ?v_26 c_4)) (= (f1 c_3 ?v_20) (f1 ?v_27 c_0)) (= (f1 c_3 ?v_21) (f1 ?v_27 c_1)) (= (f1 c_3 ?v_22) (f1 ?v_27 c_2)) (= (f1 c_3 ?v_23) (f1 ?v_27 c_3)) (= (f1 c_3 ?v_24) (f1 ?v_27 c_4)) (= (f1 c_3 ?v_25) (f1 ?v_28 c_0)) (= (f1 c_3 ?v_26) (f1 ?v_28 c_1)) (= (f1 c_3 ?v_27) (f1 ?v_28 c_2)) (= (f1 c_3 ?v_28) (f1 ?v_28 c_3)) (= (f1 c_3 ?v_29) (f1 ?v_28 c_4)) (= (f1 c_3 ?v_30) (f1 ?v_29 c_0)) (= (f1 c_3 ?v_31) (f1 ?v_29 c_1)) (= (f1 c_3 ?v_32) (f1 ?v_29 c_2)) (= (f1 c_3 ?v_33) (f1 ?v_29 c_3)) (= (f1 c_3 ?v_34) (f1 ?v_29 c_4)) (= (f1 c_4 ?v_5) (f1 ?v_30 c_0)) (= (f1 c_4 ?v_7) (f1 ?v_30 c_1)) (= (f1 c_4 ?v_9) (f1 ?v_30 c_2)) (= (f1 c_4 ?v_11) (f1 ?v_30 c_3)) (= (f1 c_4 ?v_13) (f1 ?v_30 c_4)) (= (f1 c_4 ?v_15) (f1 ?v_31 c_0)) (= (f1 c_4 ?v_16) (f1 ?v_31 c_1)) (= (f1 c_4 ?v_17) (f1 ?v_31 c_2)) (= (f1 c_4 ?v_18) (f1 ?v_31 c_3)) (= (f1 c_4 ?v_19) (f1 ?v_31 c_4)) (= (f1 c_4 ?v_20) (f1 ?v_32 c_0)) (= (f1 c_4 ?v_21) (f1 ?v_32 c_1)) (= (f1 c_4 ?v_22) (f1 ?v_32 c_2)) (= (f1 c_4 ?v_23) (f1 ?v_32 c_3)) (= (f1 c_4 ?v_24) (f1 ?v_32 c_4)) (= (f1 c_4 ?v_25) (f1 ?v_33 c_0)) (= (f1 c_4 ?v_26) (f1 ?v_33 c_1)) (= (f1 c_4 ?v_27) (f1 ?v_33 c_2)) (= (f1 c_4 ?v_28) (f1 ?v_33 c_3)) (= (f1 c_4 ?v_29) (f1 ?v_33 c_4)) (= (f1 c_4 ?v_30) (f1 ?v_34 c_0)) (= (f1 c_4 ?v_31) (f1 ?v_34 c_1)) (= (f1 c_4 ?v_32) (f1 ?v_34 c_2)) (= (f1 c_4 ?v_33) (f1 ?v_34 c_3)) (= (f1 c_4 ?v_34) (f1 ?v_34 c_4)) (or ?v_111 ?v_140) (or ?v_111 ?v_141) (or ?v_111 ?v_142) (or ?v_111 ?v_143) (or ?v_111 ?v_144) (or ?v_112 (not (= ?v_5 ?v_15))) (or ?v_112 (not (= ?v_7 ?v_16))) (or ?v_112 (not (= ?v_9 ?v_17))) (or ?v_112 (not (= ?v_11 ?v_18))) (or ?v_112 (not (= ?v_13 ?v_19))) (or ?v_113 (not (= ?v_5 ?v_20))) (or ?v_113 (not (= ?v_7 ?v_21))) (or ?v_113 (not (= ?v_9 ?v_22))) (or ?v_113 (not (= ?v_11 ?v_23))) (or ?v_113 (not (= ?v_13 ?v_24))) (or ?v_114 (not (= ?v_5 ?v_25))) (or ?v_114 (not (= ?v_7 ?v_26))) (or ?v_114 (not (= ?v_9 ?v_27))) (or ?v_114 (not (= ?v_11 ?v_28))) (or ?v_114 (not (= ?v_13 ?v_29))) (or ?v_115 (not (= ?v_5 ?v_30))) (or ?v_115 (not (= ?v_7 ?v_31))) (or ?v_115 (not (= ?v_9 ?v_32))) (or ?v_115 (not (= ?v_11 ?v_33))) (or ?v_115 (not (= ?v_13 ?v_34))) (or ?v_116 (not (= ?v_15 ?v_5))) (or ?v_116 (not (= ?v_16 ?v_7))) (or ?v_116 (not (= ?v_17 ?v_9))) (or ?v_116 (not (= ?v_18 ?v_11))) (or ?v_116 (not (= ?v_19 ?v_13))) (or ?v_118 ?v_145) (or ?v_118 ?v_146) (or ?v_118 ?v_147) (or ?v_118 ?v_148) (or ?v_118 ?v_149) (or ?v_119 (not (= ?v_15 ?v_20))) (or ?v_119 (not (= ?v_16 ?v_21))) (or ?v_119 (not (= ?v_17 ?v_22))) (or ?v_119 (not (= ?v_18 ?v_23))) (or ?v_119 (not (= ?v_19 ?v_24))) (or ?v_120 (not (= ?v_15 ?v_25))) (or ?v_120 (not (= ?v_16 ?v_26))) (or ?v_120 (not (= ?v_17 ?v_27))) (or ?v_120 (not (= ?v_18 ?v_28))) (or ?v_120 (not (= ?v_19 ?v_29))) (or ?v_121 (not (= ?v_15 ?v_30))) (or ?v_121 (not (= ?v_16 ?v_31))) (or ?v_121 (not (= ?v_17 ?v_32))) (or ?v_121 (not (= ?v_18 ?v_33))) (or ?v_121 (not (= ?v_19 ?v_34))) (or ?v_122 (not (= ?v_20 ?v_5))) (or ?v_122 (not (= ?v_21 ?v_7))) (or ?v_122 (not (= ?v_22 ?v_9))) (or ?v_122 (not (= ?v_23 ?v_11))) (or ?v_122 (not (= ?v_24 ?v_13))) (or ?v_123 (not (= ?v_20 ?v_15))) (or ?v_123 (not (= ?v_21 ?v_16))) (or ?v_123 (not (= ?v_22 ?v_17))) (or ?v_123 (not (= ?v_23 ?v_18))) (or ?v_123 (not (= ?v_24 ?v_19))) (or ?v_124 ?v_150) (or ?v_124 ?v_151) (or ?v_124 ?v_152) (or ?v_124 ?v_153) (or ?v_124 ?v_154) (or ?v_125 (not (= ?v_20 ?v_25))) (or ?v_125 (not (= ?v_21 ?v_26))) (or ?v_125 (not (= ?v_22 ?v_27))) (or ?v_125 (not (= ?v_23 ?v_28))) (or ?v_125 (not (= ?v_24 ?v_29))) (or ?v_126 (not (= ?v_20 ?v_30))) (or ?v_126 (not (= ?v_21 ?v_31))) (or ?v_126 (not (= ?v_22 ?v_32))) (or ?v_126 (not (= ?v_23 ?v_33))) (or ?v_126 (not (= ?v_24 ?v_34))) (or ?v_127 (not (= ?v_25 ?v_5))) (or ?v_127 (not (= ?v_26 ?v_7))) (or ?v_127 (not (= ?v_27 ?v_9))) (or ?v_127 (not (= ?v_28 ?v_11))) (or ?v_127 (not (= ?v_29 ?v_13))) (or ?v_128 (not (= ?v_25 ?v_15))) (or ?v_128 (not (= ?v_26 ?v_16))) (or ?v_128 (not (= ?v_27 ?v_17))) (or ?v_128 (not (= ?v_28 ?v_18))) (or ?v_128 (not (= ?v_29 ?v_19))) (or ?v_129 (not (= ?v_25 ?v_20))) (or ?v_129 (not (= ?v_26 ?v_21))) (or ?v_129 (not (= ?v_27 ?v_22))) (or ?v_129 (not (= ?v_28 ?v_23))) (or ?v_129 (not (= ?v_29 ?v_24))) (or ?v_130 ?v_155) (or ?v_130 ?v_156) (or ?v_130 ?v_157) (or ?v_130 ?v_158) (or ?v_130 ?v_159) (or ?v_131 (not (= ?v_25 ?v_30))) (or ?v_131 (not (= ?v_26 ?v_31))) (or ?v_131 (not (= ?v_27 ?v_32))) (or ?v_131 (not (= ?v_28 ?v_33))) (or ?v_131 (not (= ?v_29 ?v_34))) (or ?v_132 (not (= ?v_30 ?v_5))) (or ?v_132 (not (= ?v_31 ?v_7))) (or ?v_132 (not (= ?v_32 ?v_9))) (or ?v_132 (not (= ?v_33 ?v_11))) (or ?v_132 (not (= ?v_34 ?v_13))) (or ?v_133 (not (= ?v_30 ?v_15))) (or ?v_133 (not (= ?v_31 ?v_16))) (or ?v_133 (not (= ?v_32 ?v_17))) (or ?v_133 (not (= ?v_33 ?v_18))) (or ?v_133 (not (= ?v_34 ?v_19))) (or ?v_134 (not (= ?v_30 ?v_20))) (or ?v_134 (not (= ?v_31 ?v_21))) (or ?v_134 (not (= ?v_32 ?v_22))) (or ?v_134 (not (= ?v_33 ?v_23))) (or ?v_134 (not (= ?v_34 ?v_24))) (or ?v_135 (not (= ?v_30 ?v_25))) (or ?v_135 (not (= ?v_31 ?v_26))) (or ?v_135 (not (= ?v_32 ?v_27))) (or ?v_135 (not (= ?v_33 ?v_28))) (or ?v_135 (not (= ?v_34 ?v_29))) (or ?v_136 ?v_160) (or ?v_136 ?v_161) (or ?v_136 ?v_162) (or ?v_136 ?v_163) (or ?v_136 ?v_164) (or (= ?v_6 c_0) (= ?v_6 c_1) (= ?v_6 c_2) (= ?v_6 c_3) (= ?v_6 c_4)) (or (= ?v_8 c_0) (= ?v_8 c_1) (= ?v_8 c_2) (= ?v_8 c_3) (= ?v_8 c_4)) (or (= ?v_10 c_0) (= ?v_10 c_1) (= ?v_10 c_2) (= ?v_10 c_3) (= ?v_10 c_4)) (or (= ?v_12 c_0) (= ?v_12 c_1) (= ?v_12 c_2) (= ?v_12 c_3) (= ?v_12 c_4)) (or (= ?v_14 c_0) (= ?v_14 c_1) (= ?v_14 c_2) (= ?v_14 c_3) (= ?v_14 c_4)) (or (= ?v_35 c_0) (= ?v_35 c_1) (= ?v_35 c_2) (= ?v_35 c_3) (= ?v_35 c_4)) (or (= ?v_36 c_0) (= ?v_36 c_1) (= ?v_36 c_2) (= ?v_36 c_3) (= ?v_36 c_4)) (or (= ?v_37 c_0) (= ?v_37 c_1) (= ?v_37 c_2) (= ?v_37 c_3) (= ?v_37 c_4)) (or (= ?v_38 c_0) (= ?v_38 c_1) (= ?v_38 c_2) (= ?v_38 c_3) (= ?v_38 c_4)) (or (= ?v_39 c_0) (= ?v_39 c_1) (= ?v_39 c_2) (= ?v_39 c_3) (= ?v_39 c_4)) (or (= ?v_40 c_0) (= ?v_40 c_1) (= ?v_40 c_2) (= ?v_40 c_3) (= ?v_40 c_4)) (or (= ?v_41 c_0) (= ?v_41 c_1) (= ?v_41 c_2) (= ?v_41 c_3) (= ?v_41 c_4)) (or (= ?v_42 c_0) (= ?v_42 c_1) (= ?v_42 c_2) (= ?v_42 c_3) (= ?v_42 c_4)) (or (= ?v_43 c_0) (= ?v_43 c_1) (= ?v_43 c_2) (= ?v_43 c_3) (= ?v_43 c_4)) (or (= ?v_44 c_0) (= ?v_44 c_1) (= ?v_44 c_2) (= ?v_44 c_3) (= ?v_44 c_4)) (or (= ?v_45 c_0) (= ?v_45 c_1) (= ?v_45 c_2) (= ?v_45 c_3) (= ?v_45 c_4)) (or (= ?v_46 c_0) (= ?v_46 c_1) (= ?v_46 c_2) (= ?v_46 c_3) (= ?v_46 c_4)) (or (= ?v_47 c_0) (= ?v_47 c_1) (= ?v_47 c_2) (= ?v_47 c_3) (= ?v_47 c_4)) (or (= ?v_48 c_0) (= ?v_48 c_1) (= ?v_48 c_2) (= ?v_48 c_3) (= ?v_48 c_4)) (or (= ?v_49 c_0) (= ?v_49 c_1) (= ?v_49 c_2) (= ?v_49 c_3) (= ?v_49 c_4)) (or (= ?v_50 c_0) (= ?v_50 c_1) (= ?v_50 c_2) (= ?v_50 c_3) (= ?v_50 c_4)) (or (= ?v_51 c_0) (= ?v_51 c_1) (= ?v_51 c_2) (= ?v_51 c_3) (= ?v_51 c_4)) (or (= ?v_52 c_0) (= ?v_52 c_1) (= ?v_52 c_2) (= ?v_52 c_3) (= ?v_52 c_4)) (or (= ?v_53 c_0) (= ?v_53 c_1) (= ?v_53 c_2) (= ?v_53 c_3) (= ?v_53 c_4)) (or (= ?v_54 c_0) (= ?v_54 c_1) (= ?v_54 c_2) (= ?v_54 c_3) (= ?v_54 c_4)) (or (= ?v_5 c_0) (= ?v_5 c_1) (= ?v_5 c_2) (= ?v_5 c_3) (= ?v_5 c_4)) (or (= ?v_7 c_0) (= ?v_7 c_1) (= ?v_7 c_2) (= ?v_7 c_3) (= ?v_7 c_4)) (or (= ?v_9 c_0) (= ?v_9 c_1) (= ?v_9 c_2) (= ?v_9 c_3) (= ?v_9 c_4)) (or (= ?v_11 c_0) (= ?v_11 c_1) (= ?v_11 c_2) (= ?v_11 c_3) (= ?v_11 c_4)) (or (= ?v_13 c_0) (= ?v_13 c_1) (= ?v_13 c_2) (= ?v_13 c_3) (= ?v_13 c_4)) (or (= ?v_15 c_0) (= ?v_15 c_1) (= ?v_15 c_2) (= ?v_15 c_3) (= ?v_15 c_4)) (or (= ?v_16 c_0) (= ?v_16 c_1) (= ?v_16 c_2) (= ?v_16 c_3) (= ?v_16 c_4)) (or (= ?v_17 c_0) (= ?v_17 c_1) (= ?v_17 c_2) (= ?v_17 c_3) (= ?v_17 c_4)) (or (= ?v_18 c_0) (= ?v_18 c_1) (= ?v_18 c_2) (= ?v_18 c_3) (= ?v_18 c_4)) (or (= ?v_19 c_0) (= ?v_19 c_1) (= ?v_19 c_2) (= ?v_19 c_3) (= ?v_19 c_4)) (or (= ?v_20 c_0) (= ?v_20 c_1) (= ?v_20 c_2) (= ?v_20 c_3) (= ?v_20 c_4)) (or (= ?v_21 c_0) (= ?v_21 c_1) (= ?v_21 c_2) (= ?v_21 c_3) (= ?v_21 c_4)) (or (= ?v_22 c_0) (= ?v_22 c_1) (= ?v_22 c_2) (= ?v_22 c_3) (= ?v_22 c_4)) (or (= ?v_23 c_0) (= ?v_23 c_1) (= ?v_23 c_2) (= ?v_23 c_3) (= ?v_23 c_4)) (or (= ?v_24 c_0) (= ?v_24 c_1) (= ?v_24 c_2) (= ?v_24 c_3) (= ?v_24 c_4)) (or (= ?v_25 c_0) (= ?v_25 c_1) (= ?v_25 c_2) (= ?v_25 c_3) (= ?v_25 c_4)) (or (= ?v_26 c_0) (= ?v_26 c_1) (= ?v_26 c_2) (= ?v_26 c_3) (= ?v_26 c_4)) (or (= ?v_27 c_0) (= ?v_27 c_1) (= ?v_27 c_2) (= ?v_27 c_3) (= ?v_27 c_4)) (or (= ?v_28 c_0) (= ?v_28 c_1) (= ?v_28 c_2) (= ?v_28 c_3) (= ?v_28 c_4)) (or (= ?v_29 c_0) (= ?v_29 c_1) (= ?v_29 c_2) (= ?v_29 c_3) (= ?v_29 c_4)) (or (= ?v_30 c_0) (= ?v_30 c_1) (= ?v_30 c_2) (= ?v_30 c_3) (= ?v_30 c_4)) (or (= ?v_31 c_0) (= ?v_31 c_1) (= ?v_31 c_2) (= ?v_31 c_3) (= ?v_31 c_4)) (or (= ?v_32 c_0) (= ?v_32 c_1) (= ?v_32 c_2) (= ?v_32 c_3) (= ?v_32 c_4)) (or (= ?v_33 c_0) (= ?v_33 c_1) (= ?v_33 c_2) (= ?v_33 c_3) (= ?v_33 c_4)) (or (= ?v_34 c_0) (= ?v_34 c_1) (= ?v_34 c_2) (= ?v_34 c_3) (= ?v_34 c_4)) (or (= ?v_0 c_0) (= ?v_0 c_1) (= ?v_0 c_2) (= ?v_0 c_3) (= ?v_0 c_4)) (or (= ?v_1 c_0) (= ?v_1 c_1) (= ?v_1 c_2) (= ?v_1 c_3) (= ?v_1 c_4)) (or (= ?v_2 c_0) (= ?v_2 c_1) (= ?v_2 c_2) (= ?v_2 c_3) (= ?v_2 c_4)) (or (= ?v_3 c_0) (= ?v_3 c_1) (= ?v_3 c_2) (= ?v_3 c_3) (= ?v_3 c_4)) (or (= ?v_4 c_0) (= ?v_4 c_1) (= ?v_4 c_2) (= ?v_4 c_3) (= ?v_4 c_4)) (or (= c5 c_0) (= c5 c_1) (= c5 c_2) (= c5 c_3) (= c5 c_4)) (or (= c6 c_0) (= c6 c_1) (= c6 c_2) (= c6 c_3) (= c6 c_4)) (or (= c2 c_0) (= c2 c_1) (= c2 c_2) (= c2 c_3) (= c2 c_4))))))))))))))))))))))))))))))))
(check-sat)
(exit)
