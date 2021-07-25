Load "preamble3D.v".


(* dans la couche 0 *)
Lemma LABCMP : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: P ::  nil) = 3 -> rk(A :: B :: C :: M :: P ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HABCPeq HApBpCpPeq
.

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCMP requis par la preuve de (?)ABCMP pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCMP requis par la preuve de (?)ABCMP pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCMPm3 : rk(A :: B :: C :: M :: P :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: M :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: M :: P :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -4*)
assert(HABCMPM3 : rk(A :: B :: C :: M :: P :: nil) <= 3).
{
	assert(HABCMMtmp : rk(A :: B :: C :: M :: nil) <= 3) by (solve_hyps_max HABCMeq HABCMM3).
	assert(HABCPMtmp : rk(A :: B :: C :: P :: nil) <= 3) by (solve_hyps_max HABCPeq HABCPM3).
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hincl : incl (A :: B :: C :: nil) (list_inter (A :: B :: C :: M :: nil) (A :: B :: C :: P :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: P :: nil) (A :: B :: C :: M :: A :: B :: C :: P :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: M :: A :: B :: C :: P :: nil) ((A :: B :: C :: M :: nil) ++ (A :: B :: C :: P :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: B :: C :: M :: nil) (A :: B :: C :: P :: nil) (A :: B :: C :: nil) 3 3 3 HABCMMtmp HABCPMtmp HABCmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HABCMPM : rk(A :: B :: C :: M :: P ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCMPm : rk(A :: B :: C :: M :: P ::  nil) >= 1) by (solve_hyps_min HABCMPeq HABCMPm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCpMP : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: P ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M :: P ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HABCPeq HApBpCpPeq
.

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ApBpCpMP requis par la preuve de (?)ApBpCpMP pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ApBpCpMP requis par la preuve de (?)ApBpCpMP pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HApBpCpMPm3 : rk(Ap :: Bp :: Cp :: M :: P :: nil) >= 3).
{
	assert(HApBpCpmtmp : rk(Ap :: Bp :: Cp :: nil) >= 3) by (solve_hyps_min HApBpCpeq HApBpCpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Ap :: Bp :: Cp :: nil) (Ap :: Bp :: Cp :: M :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Ap :: Bp :: Cp :: nil) (Ap :: Bp :: Cp :: M :: P :: nil) 3 3 HApBpCpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -4*)
assert(HApBpCpMPM3 : rk(Ap :: Bp :: Cp :: M :: P :: nil) <= 3).
{
	assert(HApBpCpMMtmp : rk(Ap :: Bp :: Cp :: M :: nil) <= 3) by (solve_hyps_max HApBpCpMeq HApBpCpMM3).
	assert(HApBpCpPMtmp : rk(Ap :: Bp :: Cp :: P :: nil) <= 3) by (solve_hyps_max HApBpCpPeq HApBpCpPM3).
	assert(HApBpCpmtmp : rk(Ap :: Bp :: Cp :: nil) >= 3) by (solve_hyps_min HApBpCpeq HApBpCpm3).
	assert(Hincl : incl (Ap :: Bp :: Cp :: nil) (list_inter (Ap :: Bp :: Cp :: M :: nil) (Ap :: Bp :: Cp :: P :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Ap :: Bp :: Cp :: M :: P :: nil) (Ap :: Bp :: Cp :: M :: Ap :: Bp :: Cp :: P :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: Bp :: Cp :: M :: Ap :: Bp :: Cp :: P :: nil) ((Ap :: Bp :: Cp :: M :: nil) ++ (Ap :: Bp :: Cp :: P :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: Bp :: Cp :: M :: nil) (Ap :: Bp :: Cp :: P :: nil) (Ap :: Bp :: Cp :: nil) 3 3 3 HApBpCpMMtmp HApBpCpPMtmp HApBpCpmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HApBpCpMPM : rk(Ap :: Bp :: Cp :: M :: P ::  nil) <= 4) by (apply rk_upper_dim).
assert(HApBpCpMPm : rk(Ap :: Bp :: Cp :: M :: P ::  nil) >= 1) by (solve_hyps_min HApBpCpMPeq HApBpCpMPm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCMNP : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: P ::  nil) = 3 -> rk(A :: B :: C :: M :: N :: P ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HABCPeq HApBpCpPeq
.

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCMNP requis par la preuve de (?)ABCMNP pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCMNP requis par la preuve de (?)ABCMNP pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCMNPm3 : rk(A :: B :: C :: M :: N :: P :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: M :: N :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: M :: N :: P :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 4 et -4*)
assert(HABCMNPM3 : rk(A :: B :: C :: M :: N :: P :: nil) <= 3).
{
	assert(HABCNMtmp : rk(A :: B :: C :: N :: nil) <= 3) by (solve_hyps_max HABCNeq HABCNM3).
	assert(HABCMPeq : rk(A :: B :: C :: M :: P :: nil) = 3) by (apply LABCMP with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ; assumption).
	assert(HABCMPMtmp : rk(A :: B :: C :: M :: P :: nil) <= 3) by (solve_hyps_max HABCMPeq HABCMPM3).
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hincl : incl (A :: B :: C :: nil) (list_inter (A :: B :: C :: N :: nil) (A :: B :: C :: M :: P :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: N :: P :: nil) (A :: B :: C :: N :: A :: B :: C :: M :: P :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: N :: A :: B :: C :: M :: P :: nil) ((A :: B :: C :: N :: nil) ++ (A :: B :: C :: M :: P :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: B :: C :: N :: nil) (A :: B :: C :: M :: P :: nil) (A :: B :: C :: nil) 3 3 3 HABCNMtmp HABCMPMtmp HABCmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HABCMNPM : rk(A :: B :: C :: M :: N :: P ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCMNPm : rk(A :: B :: C :: M :: N :: P ::  nil) >= 1) by (solve_hyps_min HABCMNPeq HABCMNPm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCpMNP : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: P ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M :: N :: P ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HABCPeq HApBpCpPeq
.

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ApBpCpMNP requis par la preuve de (?)ApBpCpMNP pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ApBpCpMNP requis par la preuve de (?)ApBpCpMNP pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HApBpCpMNPm3 : rk(Ap :: Bp :: Cp :: M :: N :: P :: nil) >= 3).
{
	assert(HApBpCpmtmp : rk(Ap :: Bp :: Cp :: nil) >= 3) by (solve_hyps_min HApBpCpeq HApBpCpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Ap :: Bp :: Cp :: nil) (Ap :: Bp :: Cp :: M :: N :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Ap :: Bp :: Cp :: nil) (Ap :: Bp :: Cp :: M :: N :: P :: nil) 3 3 HApBpCpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 4 et -4*)
assert(HApBpCpMNPM3 : rk(Ap :: Bp :: Cp :: M :: N :: P :: nil) <= 3).
{
	assert(HApBpCpNMtmp : rk(Ap :: Bp :: Cp :: N :: nil) <= 3) by (solve_hyps_max HApBpCpNeq HApBpCpNM3).
	assert(HApBpCpMPeq : rk(Ap :: Bp :: Cp :: M :: P :: nil) = 3) by (apply LApBpCpMP with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ; assumption).
	assert(HApBpCpMPMtmp : rk(Ap :: Bp :: Cp :: M :: P :: nil) <= 3) by (solve_hyps_max HApBpCpMPeq HApBpCpMPM3).
	assert(HApBpCpmtmp : rk(Ap :: Bp :: Cp :: nil) >= 3) by (solve_hyps_min HApBpCpeq HApBpCpm3).
	assert(Hincl : incl (Ap :: Bp :: Cp :: nil) (list_inter (Ap :: Bp :: Cp :: N :: nil) (Ap :: Bp :: Cp :: M :: P :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Ap :: Bp :: Cp :: M :: N :: P :: nil) (Ap :: Bp :: Cp :: N :: Ap :: Bp :: Cp :: M :: P :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: Bp :: Cp :: N :: Ap :: Bp :: Cp :: M :: P :: nil) ((Ap :: Bp :: Cp :: N :: nil) ++ (Ap :: Bp :: Cp :: M :: P :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: Bp :: Cp :: N :: nil) (Ap :: Bp :: Cp :: M :: P :: nil) (Ap :: Bp :: Cp :: nil) 3 3 3 HApBpCpNMtmp HApBpCpMPMtmp HApBpCpmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HApBpCpMNPM : rk(Ap :: Bp :: Cp :: M :: N :: P ::  nil) <= 4) by (apply rk_upper_dim).
assert(HApBpCpMNPm : rk(Ap :: Bp :: Cp :: M :: N :: P ::  nil) >= 1) by (solve_hyps_min HApBpCpMNPeq HApBpCpMNPm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCApBpCpMNP : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: P ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp :: M :: N :: P ::  nil) = 4.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HABCPeq HApBpCpPeq
.

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCApBpCpMNP requis par la preuve de (?)ABCApBpCpMNP pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCApBpCpMNP requis par la preuve de (?)ABCApBpCpMNP pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCApBpCpMNPm3 : rk(A :: B :: C :: Ap :: Bp :: Cp :: M :: N :: P :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: Ap :: Bp :: Cp :: M :: N :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: Ap :: Bp :: Cp :: M :: N :: P :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCApBpCpMNPm4 : rk(A :: B :: C :: Ap :: Bp :: Cp :: M :: N :: P :: nil) >= 4).
{
	assert(HABCApBpCpmtmp : rk(A :: B :: C :: Ap :: Bp :: Cp :: nil) >= 4) by (solve_hyps_min HABCApBpCpeq HABCApBpCpm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: Bp :: Cp :: nil) (A :: B :: C :: Ap :: Bp :: Cp :: M :: N :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: Bp :: Cp :: nil) (A :: B :: C :: Ap :: Bp :: Cp :: M :: N :: P :: nil) 4 4 HABCApBpCpmtmp Hcomp Hincl);apply HT.
}

assert(HABCApBpCpMNPM : rk(A :: B :: C :: Ap :: Bp :: Cp :: M :: N :: P ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCApBpCpMNPm : rk(A :: B :: C :: Ap :: Bp :: Cp :: M :: N :: P ::  nil) >= 1) by (solve_hyps_min HABCApBpCpMNPeq HABCApBpCpMNPm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LMNP : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: P ::  nil) = 3 -> rk(M :: N :: P ::  nil) = 2.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HABCPeq HApBpCpPeq
.

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour MNP requis par la preuve de (?)MNP pour la règle 3  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour MNP requis par la preuve de (?)MNP pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HMNPm2 : rk(M :: N :: P :: nil) >= 2).
{
	assert(HMNmtmp : rk(M :: N :: nil) >= 2) by (solve_hyps_min HMNeq HMNm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (M :: N :: nil) (M :: N :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (M :: N :: nil) (M :: N :: P :: nil) 2 2 HMNmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 3 code (6 dans la thèse) *)
(* marque des antécédents A B AUB: 4 4 et 4*)
assert(HMNPM2 : rk(M :: N :: P :: nil) <= 2).
{
	assert(HABCMNPeq : rk(A :: B :: C :: M :: N :: P :: nil) = 3) by (apply LABCMNP with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ; assumption).
	assert(HABCMNPMtmp : rk(A :: B :: C :: M :: N :: P :: nil) <= 3) by (solve_hyps_max HABCMNPeq HABCMNPM3).
	assert(HApBpCpMNPeq : rk(Ap :: Bp :: Cp :: M :: N :: P :: nil) = 3) by (apply LApBpCpMNP with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ; assumption).
	assert(HApBpCpMNPMtmp : rk(Ap :: Bp :: Cp :: M :: N :: P :: nil) <= 3) by (solve_hyps_max HApBpCpMNPeq HApBpCpMNPM3).
	assert(HABCApBpCpMNPeq : rk(A :: B :: C :: Ap :: Bp :: Cp :: M :: N :: P :: nil) = 4) by (apply LABCApBpCpMNP with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ; assumption).
	assert(HABCApBpCpMNPmtmp : rk(A :: B :: C :: Ap :: Bp :: Cp :: M :: N :: P :: nil) >= 4) by (solve_hyps_min HABCApBpCpMNPeq HABCApBpCpMNPm4).
	assert(Hincl : incl (M :: N :: P :: nil) (list_inter (A :: B :: C :: M :: N :: P :: nil) (Ap :: Bp :: Cp :: M :: N :: P :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: Bp :: Cp :: M :: N :: P :: nil) (A :: B :: C :: M :: N :: P :: Ap :: Bp :: Cp :: M :: N :: P :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: M :: N :: P :: Ap :: Bp :: Cp :: M :: N :: P :: nil) ((A :: B :: C :: M :: N :: P :: nil) ++ (Ap :: Bp :: Cp :: M :: N :: P :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApBpCpMNPmtmp;try rewrite HT2 in HABCApBpCpMNPmtmp.
	assert(HT := rule_3 (A :: B :: C :: M :: N :: P :: nil) (Ap :: Bp :: Cp :: M :: N :: P :: nil) (M :: N :: P :: nil) 3 3 4 HABCMNPMtmp HApBpCpMNPMtmp HABCApBpCpMNPmtmp Hincl);apply HT.
}


assert(HMNPM : rk(M :: N :: P ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HMNPeq HMNPM3).
assert(HMNPm : rk(M :: N :: P ::  nil) >= 1) by (solve_hyps_min HMNPeq HMNPm1).
intuition.
Qed.

(* dans la couche 0 *)
Theorem def_Conclusion : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: P ::  nil) = 3 -> 
	 rk(M :: N :: P ::  nil) = 2  .
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HABCPeq HApBpCpPeq
.
repeat split.

	apply LMNP with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ; assumption.
Qed .
