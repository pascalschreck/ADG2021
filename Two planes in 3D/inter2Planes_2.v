Load "preamble3D.v".


(* dans la couche 0 *)
Lemma LABCMN : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(M :: N :: P ::  nil) = 2 ->
rk(A :: B :: C :: M :: N ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HMNPeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCMN requis par la preuve de (?)ABCMN pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCMN requis par la preuve de (?)ABCMN pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCMNm3 : rk(A :: B :: C :: M :: N :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: M :: N :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: M :: N :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -4*)
assert(HABCMNM3 : rk(A :: B :: C :: M :: N :: nil) <= 3).
{
	assert(HABCMMtmp : rk(A :: B :: C :: M :: nil) <= 3) by (solve_hyps_max HABCMeq HABCMM3).
	assert(HABCNMtmp : rk(A :: B :: C :: N :: nil) <= 3) by (solve_hyps_max HABCNeq HABCNM3).
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hincl : incl (A :: B :: C :: nil) (list_inter (A :: B :: C :: M :: nil) (A :: B :: C :: N :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: N :: nil) (A :: B :: C :: M :: A :: B :: C :: N :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: M :: A :: B :: C :: N :: nil) ((A :: B :: C :: M :: nil) ++ (A :: B :: C :: N :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: B :: C :: M :: nil) (A :: B :: C :: N :: nil) (A :: B :: C :: nil) 3 3 3 HABCMMtmp HABCNMtmp HABCmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HABCMNM : rk(A :: B :: C :: M :: N ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCMNm : rk(A :: B :: C :: M :: N ::  nil) >= 1) by (solve_hyps_min HABCMNeq HABCMNm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCpMN : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(M :: N :: P ::  nil) = 2 ->
rk(Ap :: Bp :: Cp :: M :: N ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HMNPeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ApBpCpMN requis par la preuve de (?)ApBpCpMN pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ApBpCpMN requis par la preuve de (?)ApBpCpMN pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HApBpCpMNm3 : rk(Ap :: Bp :: Cp :: M :: N :: nil) >= 3).
{
	assert(HApBpCpmtmp : rk(Ap :: Bp :: Cp :: nil) >= 3) by (solve_hyps_min HApBpCpeq HApBpCpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Ap :: Bp :: Cp :: nil) (Ap :: Bp :: Cp :: M :: N :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Ap :: Bp :: Cp :: nil) (Ap :: Bp :: Cp :: M :: N :: nil) 3 3 HApBpCpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -4*)
assert(HApBpCpMNM3 : rk(Ap :: Bp :: Cp :: M :: N :: nil) <= 3).
{
	assert(HApBpCpMMtmp : rk(Ap :: Bp :: Cp :: M :: nil) <= 3) by (solve_hyps_max HApBpCpMeq HApBpCpMM3).
	assert(HApBpCpNMtmp : rk(Ap :: Bp :: Cp :: N :: nil) <= 3) by (solve_hyps_max HApBpCpNeq HApBpCpNM3).
	assert(HApBpCpmtmp : rk(Ap :: Bp :: Cp :: nil) >= 3) by (solve_hyps_min HApBpCpeq HApBpCpm3).
	assert(Hincl : incl (Ap :: Bp :: Cp :: nil) (list_inter (Ap :: Bp :: Cp :: M :: nil) (Ap :: Bp :: Cp :: N :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Ap :: Bp :: Cp :: M :: N :: nil) (Ap :: Bp :: Cp :: M :: Ap :: Bp :: Cp :: N :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: Bp :: Cp :: M :: Ap :: Bp :: Cp :: N :: nil) ((Ap :: Bp :: Cp :: M :: nil) ++ (Ap :: Bp :: Cp :: N :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: Bp :: Cp :: M :: nil) (Ap :: Bp :: Cp :: N :: nil) (Ap :: Bp :: Cp :: nil) 3 3 3 HApBpCpMMtmp HApBpCpNMtmp HApBpCpmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HApBpCpMNM : rk(Ap :: Bp :: Cp :: M :: N ::  nil) <= 4) by (apply rk_upper_dim).
assert(HApBpCpMNm : rk(Ap :: Bp :: Cp :: M :: N ::  nil) >= 1) by (solve_hyps_min HApBpCpMNeq HApBpCpMNm1).
intuition.
Qed.

(* dans constructLemma(), requis par LApBpCpP *)
(* dans la couche 0 *)
Lemma LApBpCpMNP : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(M :: N :: P ::  nil) = 2 ->
rk(Ap :: Bp :: Cp :: M :: N :: P ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HMNPeq .

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
(* marque des antécédents A B AiB : 4 -4 et -4*)
assert(HApBpCpMNPM3 : rk(Ap :: Bp :: Cp :: M :: N :: P :: nil) <= 3).
{
	assert(HApBpCpMNeq : rk(Ap :: Bp :: Cp :: M :: N :: nil) = 3) by (apply LApBpCpMN with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ; assumption).
	assert(HApBpCpMNMtmp : rk(Ap :: Bp :: Cp :: M :: N :: nil) <= 3) by (solve_hyps_max HApBpCpMNeq HApBpCpMNM3).
	assert(HMNPMtmp : rk(M :: N :: P :: nil) <= 2) by (solve_hyps_max HMNPeq HMNPM2).
	assert(HMNmtmp : rk(M :: N :: nil) >= 2) by (solve_hyps_min HMNeq HMNm2).
	assert(Hincl : incl (M :: N :: nil) (list_inter (Ap :: Bp :: Cp :: M :: N :: nil) (M :: N :: P :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Ap :: Bp :: Cp :: M :: N :: P :: nil) (Ap :: Bp :: Cp :: M :: N :: M :: N :: P :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: Bp :: Cp :: M :: N :: M :: N :: P :: nil) ((Ap :: Bp :: Cp :: M :: N :: nil) ++ (M :: N :: P :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: Bp :: Cp :: M :: N :: nil) (M :: N :: P :: nil) (M :: N :: nil) 3 2 2 HApBpCpMNMtmp HMNPMtmp HMNmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HApBpCpMNPM : rk(Ap :: Bp :: Cp :: M :: N :: P ::  nil) <= 4) by (apply rk_upper_dim).
assert(HApBpCpMNPm : rk(Ap :: Bp :: Cp :: M :: N :: P ::  nil) >= 1) by (solve_hyps_min HApBpCpMNPeq HApBpCpMNPm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCpP : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(M :: N :: P ::  nil) = 2 ->
rk(Ap :: Bp :: Cp :: P ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HMNPeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ApBpCpP requis par la preuve de (?)ApBpCpP pour la règle 6  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ApBpCpP requis par la preuve de (?)ApBpCpP pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HApBpCpPm3 : rk(Ap :: Bp :: Cp :: P :: nil) >= 3).
{
	assert(HApBpCpmtmp : rk(Ap :: Bp :: Cp :: nil) >= 3) by (solve_hyps_min HApBpCpeq HApBpCpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Ap :: Bp :: Cp :: nil) (Ap :: Bp :: Cp :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Ap :: Bp :: Cp :: nil) (Ap :: Bp :: Cp :: P :: nil) 3 3 HApBpCpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 6 (code, 3 ou 4 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HApBpCpPM3 : rk(Ap :: Bp :: Cp :: P :: nil) <= 3).
{
	assert(HApBpCpMNPeq : rk(Ap :: Bp :: Cp :: M :: N :: P :: nil) = 3) by (apply LApBpCpMNP with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ; assumption).
	assert(HApBpCpMNPMtmp : rk(Ap :: Bp :: Cp :: M :: N :: P :: nil) <= 3) by (solve_hyps_max HApBpCpMNPeq HApBpCpMNPM3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Ap :: Bp :: Cp :: P :: nil) (Ap :: Bp :: Cp :: M :: N :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (Ap :: Bp :: Cp :: P :: nil) (Ap :: Bp :: Cp :: M :: N :: P :: nil) 3 3 HApBpCpMNPMtmp Hcomp Hincl);apply HT.
}

assert(HApBpCpPM : rk(Ap :: Bp :: Cp :: P ::  nil) <= 4) by (apply rk_upper_dim).
assert(HApBpCpPm : rk(Ap :: Bp :: Cp :: P ::  nil) >= 1) by (solve_hyps_min HApBpCpPeq HApBpCpPm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCMNP : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(M :: N :: P ::  nil) = 2 ->
rk(A :: B :: C :: M :: N :: P ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HMNPeq .

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
(* marque des antécédents A B AiB : 4 -4 et -4*)
assert(HABCMNPM3 : rk(A :: B :: C :: M :: N :: P :: nil) <= 3).
{
	assert(HABCMNeq : rk(A :: B :: C :: M :: N :: nil) = 3) by (apply LABCMN with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ; assumption).
	assert(HABCMNMtmp : rk(A :: B :: C :: M :: N :: nil) <= 3) by (solve_hyps_max HABCMNeq HABCMNM3).
	assert(HMNPMtmp : rk(M :: N :: P :: nil) <= 2) by (solve_hyps_max HMNPeq HMNPM2).
	assert(HMNmtmp : rk(M :: N :: nil) >= 2) by (solve_hyps_min HMNeq HMNm2).
	assert(Hincl : incl (M :: N :: nil) (list_inter (A :: B :: C :: M :: N :: nil) (M :: N :: P :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: N :: P :: nil) (A :: B :: C :: M :: N :: M :: N :: P :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: M :: N :: M :: N :: P :: nil) ((A :: B :: C :: M :: N :: nil) ++ (M :: N :: P :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: B :: C :: M :: N :: nil) (M :: N :: P :: nil) (M :: N :: nil) 3 2 2 HABCMNMtmp HMNPMtmp HMNmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HABCMNPM : rk(A :: B :: C :: M :: N :: P ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCMNPm : rk(A :: B :: C :: M :: N :: P ::  nil) >= 1) by (solve_hyps_min HABCMNPeq HABCMNPm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCP : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(M :: N :: P ::  nil) = 2 ->
rk(A :: B :: C :: P ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HMNPeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCP requis par la preuve de (?)ABCP pour la règle 6  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCP requis par la preuve de (?)ABCP pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCPm3 : rk(A :: B :: C :: P :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: P :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 6 (code, 3 ou 4 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCPM3 : rk(A :: B :: C :: P :: nil) <= 3).
{
	assert(HABCMNPeq : rk(A :: B :: C :: M :: N :: P :: nil) = 3) by (apply LABCMNP with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ; assumption).
	assert(HABCMNPMtmp : rk(A :: B :: C :: M :: N :: P :: nil) <= 3) by (solve_hyps_max HABCMNPeq HABCMNPM3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: P :: nil) (A :: B :: C :: M :: N :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (A :: B :: C :: P :: nil) (A :: B :: C :: M :: N :: P :: nil) 3 3 HABCMNPMtmp Hcomp Hincl);apply HT.
}

assert(HABCPM : rk(A :: B :: C :: P ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCPm : rk(A :: B :: C :: P ::  nil) >= 1) by (solve_hyps_min HABCPeq HABCPm1).
intuition.
Qed.

(* dans la couche 0 *)
Theorem def_Conclusion : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(M :: N :: P ::  nil) = 2 ->

	 rk(A :: B :: C :: P ::  nil) = 3  /\ 
	 rk(Ap :: Bp :: Cp :: P ::  nil) = 3  .
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HMNPeq .
repeat split.

	apply LABCP with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ; assumption.

	apply LApBpCpP with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ; assumption.
Qed .
