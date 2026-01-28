(* weakestpre.v *)

From iris.proofmode Require Import base tactics.
From iris.base_logic Require Import invariants.
From complete_iris.base_logic Require Import ghost_bag.
From iris.program_logic Require Export lifting.
From complete_iris.program_logic Require Export state adequacy.
From iris.heap_lang Require Import primitive_laws notation.

Class requisiteG Σ := RequisiteG {
  #[local] requisiteG_bag :: ghost_bagG Σ expr;
}.

Definition requisiteΣ := #[ghost_bagΣ expr].

Global Instance subG_requisiteG Σ : subG requisiteΣ Σ → requisiteG Σ.
Proof. solve_inG. Qed.

(* TODO: generalize over stuckness *)
Section weakestpre.
  Context `{!heapGS Σ, !requisiteG Σ}.
  Implicit Types (e : expr) (v : val) (σ : state) (t : list expr) (Q : val → state → Prop).
  Notation safe_tp s t1 σ1 := (∀ t2 σ2 e2, s = NotStuck →
    rtc erased_step (t1, σ1) (t2, σ2) → e2 ∈ t2 → not_stuck e2 σ2).

  Definition safeInv γb : iProp Σ :=
    ∃ t2 σl nsl κsl ntl, own_state σl nsl κsl ntl ∗ ghost_bag_auth γb (list_to_set_disj t2) ∗
      ⌜safe_tp NotStuck t2 σl ⌝.

  Local Lemma wptp_safe_inv t γb :
    inv nroot (safeInv γb) ⊢
    [∗ list] e ∈ t, ghost_bag_frag γb e -∗ WP e {{ _, True }}.
  Proof.
    iIntros "#Hinv".
    iLöb as "IH" forall (t).
    iApply (big_sepL_impl (λ _ _, emp)%I); first done.
    iIntros "!#" (tid e _) "_ He◯".
    destruct (to_val e) as [v|] eqn:He.

    - rewrite -(of_to_val e v); last apply He.
      by iApply wp_value.

    - iApply wp_lift_step_fupd; first done.
      iIntros (σ1 ns κ κs nt) "Hstate_interp".
      iInv nroot as (t1 σl1 nsl κl ntl) ">(Hown_state & Ht● & %Hsafe)" "Hclose1".
      iApply fupd_mask_intro; first set_solver. iIntros "Hclose2".
      iDestruct (own_state_agree with "Hstate_interp Hown_state") as %Hσlσ.
      iDestruct (ghost_bag_elem_of with "Ht● He◯") as %Hint1%elem_of_list_to_set_disj.

      assert (He_red : reducible e σl1). {
        specialize (Hsafe t1 σl1 e).
        destruct Hsafe as [Hfalse|]; try done.
        rewrite /= He in Hfalse. by inversion Hfalse.
      }

      iSplit; first by iPureIntro; eapply reducible_mono.
      iIntros (e2 σ2 efs Hprim_step) "_ !>!>".

      (* update ghost resources *)
      iMod (ghost_bag_update _ _ e2 with "Ht● He◯") as "[Ht● He◯]".
      iMod (ghost_bag_insert_big (list_to_set_disj efs) with "Ht●") as "[Ht● Hefs◯]".
      iAssert ([∗ list] k ∈ efs, ghost_bag_frag γb k)%I with "[Hefs◯]" as "Hefs◯".
      { clear.
        iInduction efs as [|ef efs] "IHf"; first done.
        rewrite big_opL_cons list_to_set_disj_cons big_opMS_insert.
        iDestruct "Hefs◯" as "[$ Hefs◯]".
        by iApply "IHf". }
      edestruct (prim_step_subset) as (σ_ext & σl2 & Hσl1_dis & Hσl2_dis & Heq1 & Heq2 & Hprim_step_l).
      { exact Hσlσ. } { exact He_red. } { exact Hprim_step. }
      subst σ1 σ2.
      iMod (state_update with "Hstate_interp Hown_state") as "[$ Hown_state]".
      { exact Hσl1_dis. } { exact Hσl2_dis. } { exact Hprim_step_l. }

      iMod "Hclose2" as "_".
      iMod ("Hclose1" with "[Ht● $Hown_state]") as "_".
      { destruct (elem_of_list_split t1 e Hint1) as (t1a & t1b & ->).
        iEval (rewrite Permutation_app_comm -app_comm_cons list_to_set_disj_cons) in "Ht●".
        replace (({[+ e +]} ⊎ list_to_set_disj (t1b ++ t1a)) ∖ {[+ e +]})
          with (list_to_set_disj (t1b ++ t1a) : gmultiset expr)
          by multiset_solver.
        iEval (rewrite -list_to_set_disj_cons app_comm_cons Permutation_app_comm) in "Ht●".
        iEval (rewrite comm -list_to_set_disj_app) in "Ht●".
        rewrite -!assoc -app_comm_cons.

        iFrame "Ht●". iIntros "!>!%".
        intros t3 σ3 e3 _ Hsteps.
        apply Hsafe; first done.
        eapply rtc_l; last exact Hsteps.
        exists κ.
        by apply (step_atomic e σl1 e2 σl2 efs t1a t1b). }

      iModIntro. simpl.
      iCombine "He◯ Hefs◯" as "Ht◯".
      rewrite -(big_sepL_cons (λ _ e, ghost_bag_frag γb e)).
      rewrite -(big_sepL_cons (λ _ e, WP e {{_, True}})%I).
      iApply (big_sepL_wand with "Ht◯").
      iApply "IH".
  Qed.

  Lemma wptp_safe t P :
    (∀ σ, P σ → safe_tp NotStuck t σ) →
    ⌞P⌟ ⊢ |={⊤}=> [∗ list] e ∈ t, WP e {{ _, True }}.
  Proof.
    iIntros (Hsafe) "HP".
    iDestruct "HP" as (σl nsl κsl ntl) "[Hown_state %HP]".
    specialize (Hsafe σl HP).
    iMod (ghost_bag_alloc_big (list_to_set_disj t)) as (γb) "[Ht● Ht◯]".
    iAssert ([∗ list] k ∈ t, ghost_bag_frag γb k)%I with "[Ht◯]" as "Ht◯".
    { clear.
      iInduction t as [|e t] "IH"; first done.
      rewrite big_opL_cons list_to_set_disj_cons big_opMS_insert.
      iDestruct "Ht◯" as "[$ Ht◯]".
      by iApply "IH". }
    iMod (inv_alloc nroot ⊤ (safeInv γb) with "[$Hown_state $Ht● //]") as "#Hinv".
    iModIntro.
    iApply (big_sepL_wand with "Ht◯").
    by iApply wptp_safe_inv.
  Qed.

  Theorem wp_requisiteness_nofork e (P : state → Prop) (Q : val → state → Prop) :
    (∀ σ, P σ → adequate_nofork NotStuck e σ Q) →
    ⌞P⌟ ⊢ WP e {{ v, ⌞Q v⌟ }}.
  Proof.
    iIntros (Hadq) "HP".
    iLöb as "IH" forall (e P Hadq).
    destruct (to_val e) as [v|] eqn:He.

    - rewrite -(of_to_val e v); last apply He.
      rewrite -(of_to_val e v) in Hadq; last apply He.
      iApply wp_value.
      iDestruct "HP" as (σ ns κs nt) "[Hown %Hσ]".
      iFrame. iPureIntro.
      by apply (adequate_nofork_result NotStuck (of_val v) σ Q (Hadq σ Hσ) [] σ v).

    - iApply wp_lift_step_fupd; first done.
      iIntros (σ1 ns κ κs nt) "Hstate_interp".
      iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
      iDestruct "HP" as (σl1 nsl κl ntl) "[Hσl %HPσl]".
      iDestruct (own_state_agree with "Hstate_interp Hσl") as %Hσlσ.
      specialize (Hadq σl1 HPσl).

      assert (He_red : reducible e σl1). {
        pose proof (adequate_nofork_not_stuck _ _ _ _ Hadq) as Hnot_stuck.
        specialize (Hnot_stuck [e] σl1 e).
        destruct Hnot_stuck as [Hfalse|]; try done.
        - set_solver.
        - rewrite /= He in Hfalse. by inversion Hfalse.
      }

      iSplit; first by iPureIntro; eapply reducible_mono.
      iIntros (e2 σ2 efs Hprim_step) "_ !>!>". iMod "Hclose" as "_".
      edestruct (prim_step_subset) as (σ_ext & σl2 & Hσl1_dis & Hσl2_dis & Heq1 & Heq2 & Hprim_step_l).
      { exact Hσlσ. } { exact He_red. } { exact Hprim_step. }
      subst σ1 σ2.
      iMod (state_update with "Hstate_interp Hσl") as "[$ Hσl]".
      { exact Hσl1_dis. } { exact Hσl2_dis. } { exact Hprim_step_l. }
      iModIntro.

      assert (efs = []) as ->.
      { cut (length (e2::efs) = 1).
        { simpl. intros ?. apply nil_length_inv. lia. }
        pose proof (adequate_nofork_nofork _ _ _ _ Hadq) as Hnofork.
        apply (Hnofork (e2::efs) σl2).
        eapply rtc_l; last apply rtc_refl.
        exists κ.
        by apply (step_atomic e σl1 e2 σl2 efs [] []). }
      rewrite big_sepL_nil (right_id emp%I).
      iApply ("IH" $! e2 (λ σ, σ=σl2) with "[] [$Hσl]"); last done.
      iPureIntro. intros ? ->.
      eapply adequate_nofork_prim_step; first exact Hprim_step_l.
      assumption.
  Qed.

  Corollary hoare_requisiteness_nofork e (P : state → Prop) (Q : val → state → Prop) :
    to_val e = None → (∀ σ, P σ → adequate_nofork NotStuck e σ Q) →
    ⊢ {{{ ⌞P⌟ }}} e {{{ v, RET v; ⌞Q v⌟ }}}.
  Proof.
    iIntros (He Hadq Φ) "!# HP HΦ".

    iApply wp_lift_step_fupd; first done.
    iIntros (σ1 ns κ κs nt) "Hstate_interp".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iDestruct "HP" as (σl1 nsl κl ntl) "[Hσl %HPσl]".
    iDestruct (own_state_agree with "Hstate_interp Hσl") as %Hσlσ.
    specialize (Hadq σl1 HPσl).

    assert (He_red : reducible e σl1). {
      pose proof (adequate_nofork_not_stuck _ _ _ _ Hadq) as Hnot_stuck.
      specialize (Hnot_stuck [e] σl1 e).
      destruct Hnot_stuck as [Hfalse|]; try done.
      - set_solver.
      - rewrite /= He in Hfalse. by inversion Hfalse.
    }

    iSplit; first by iPureIntro; eapply reducible_mono.
    iIntros (e2 σ2 efs Hprim_step) "_ !>!>". iMod "Hclose" as "_".
    edestruct (prim_step_subset) as (σ_ext & σl2 & Hσl1_dis & Hσl2_dis & Heq1 & Heq2 & Hprim_step_l).
    { exact Hσlσ. } { exact He_red. } { exact Hprim_step. }
    subst σ1 σ2.
    iMod (state_update with "Hstate_interp Hσl") as "[$ Hσl]".
    { exact Hσl1_dis. } { exact Hσl2_dis. } { exact Hprim_step_l. }
    iModIntro.

    assert (efs = []) as ->.
    { cut (length (e2::efs) = 1).
      { simpl. intros ?. apply nil_length_inv. lia. }
      pose proof (adequate_nofork_nofork _ _ _ _ Hadq) as Hnofork.
      apply (Hnofork (e2::efs) σl2).
      eapply rtc_l; last apply rtc_refl.
      exists κ.
      by apply (step_atomic e σl1 e2 σl2 efs [] []). }
    rewrite big_sepL_nil (right_id emp%I).
    iAssert (⌞λ σ, σ=σl2⌟)%I with "[$Hσl]" as "HP"; first done.
    iApply (wp_wand with "[HP] HΦ").
    iApply (wp_requisiteness_nofork with "HP").
    intros ? ->.
    eapply adequate_nofork_prim_step; first exact Hprim_step_l.
    assumption.
  Qed.

  (* False *)
  Lemma wptp_requisiteness e t (P : state → Prop) (Q : val → state → Prop) :
    (∀ σ, P σ → adequate_tp NotStuck (e::t) σ Q) →
    ⌞P⌟ ⊢ |={⊤}=> WP e {{ v, ⌞Q v⌟ }} ∗ [∗ list] e ∈ t, WP e {{ _, True }}.
  Abort.
End weakestpre.
