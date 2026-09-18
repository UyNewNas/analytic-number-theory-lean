import LiuWang.Proof.ExplicitPerron.Series

/-!
# Generic Perron series trust audit

This is a bounded compile/audit probe for the exact-same-pin Liu--Wang generic
coefficient-sequence layer after removing its character-specialized
`PerronSeries.Interchange` import.  The focused surface is deliberately small.
-/

#print axioms LiuWang.Proof.ExplicitPerron.vertical_eq_tsum
#print axioms LiuWang.Proof.ExplicitPerron.summable_majorant
#print axioms LiuWang.Proof.ExplicitPerron.tsum_stepTerm
#print axioms LiuWang.Proof.ExplicitPerron.norm_vertical_sub_sum_le
