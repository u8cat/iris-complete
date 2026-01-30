From iris.proofmode Require Import base tactics.
From iris.base_logic Require Import ghost_map invariants.
From iris.program_logic Require Export lifting.
From complete_iris.program_logic Require Export adequacy.

Class coirisG_gen (hlc : has_lc) (Λ : language) (Σ: gFunctors) `{!irisGS_gen hlc Λ Σ} := CoirisG {
  substate : relation (state Λ);
  state_disjoint : relation (state Λ);
  state_union : state Λ → state Λ → state Λ;

  own_state : state Λ → nat → list (observation Λ) → nat → iProp Σ;
  #[local] own_state_timeless σ ns κ nt :: Timeless (own_state σ ns κ nt);

  fork_post_trivial v : ⊢ fork_post v;

  reducible_mono e σ σ':
    substate σ σ' → reducible e σ → reducible e σ';

  prim_step_subset e σ κ e' σ' efs σl :
    substate σl σ → reducible e σl → prim_step e σ κ e' σ' efs →
    ∃ σ_ext σl', state_disjoint σl σ_ext ∧ state_disjoint σl' σ_ext ∧ σ = state_union σl σ_ext ∧ σ' = state_union σl' σ_ext ∧ prim_step e σl κ e' σl' efs;

  own_state_agree σ ns κs nt σ' ns' κs' nt' :
    state_interp σ ns κs nt -∗ own_state σ' ns' κs' nt' -∗ ⌜substate σ' σ⌝;

  state_update e e' σ σ' σ_ext ns ns' κ κs κ' nt nt' efs :
    state_disjoint σ σ_ext → state_disjoint σ' σ_ext → prim_step e σ κ e' σ' efs →
    state_interp (state_union σ σ_ext) ns (κ++κs) nt -∗ own_state σ ns' κ' nt' ={∅}=∗
    state_interp (state_union σ' σ_ext) (S ns) κs (length efs + nt) ∗ own_state σ' (S ns) κs (length efs + nt);
}.
Global Arguments CoirisG {hlc Λ Σ _}.

Notation coirisG Λ Σ := (coirisG_gen HasLc Λ Σ).

Definition stateful_pure `{!irisGS_gen hlc Λ Σ, !coirisG_gen hlc Λ Σ} (P : state Λ → Prop) : iProp Σ :=
  ∃ σ ns κs nt, own_state σ ns κs nt ∗ ⌜P σ⌝.
Global Arguments stateful_pure {_ _ _ _ _} _%_stdpp_scope.
Notation "⌞ P ⌟" := (stateful_pure P) (format "⌞ P ⌟") : bi_scope.

Class requisiteG Λ Σ := RequisiteG {
  #[local] requisiteG_bag :: ghost_mapG Σ nat (expr Λ);
}.

Definition requisiteΣ Λ := #[ghost_mapΣ nat (expr Λ)].

Global Instance subG_requisiteG Λ Σ :
  subG (requisiteΣ Λ) Σ → requisiteG Λ Σ.
Proof. solve_inG. Qed.

Section requisiteness.
  Context `{!irisGS_gen hlc Λ Σ, !coirisG_gen hlc Λ Σ, !requisiteG Λ Σ}.

  Implicit Types (e : expr Λ) (v : val Λ) (σ : state Λ) (t : list (expr Λ)) (Q : (val Λ) → (state Λ) → Prop).
  Notation safe_tp s t1 σ1 := (∀ t2 σ2 e2, s = NotStuck →
    rtc erased_step (t1, σ1) (t2, σ2) → e2 ∈ t2 → not_stuck e2 σ2).

  Local Instance into_val_val v : IntoVal (of_val v) v.
  Proof. done. Qed.

  Definition safeInv γb : iProp Σ :=
    ∃ t2 σl nsl κsl ntl, own_state σl nsl κsl ntl ∗
      ghost_map_auth γb 1 (list_to_map (zip (seq 0 (length t2)) t2)) ∗
      ⌜safe_tp NotStuck t2 σl ⌝.

  (* TOOD: move to stdpp *)
  Local Lemma zip_cons {A B} (a : A) (l : list A) (b : B) (k : list B) :
    zip (a::l) (b::k) = (a,b)::zip l k.
  Proof. done. Qed.
  Local Lemma zip_app {A B} (l1 l2 : list A) (k1 k2 : list B) :
    length l1 = length k1 → zip (l1++l2) (k1++k2) = zip l1 k1 ++ zip l2 k2.
  Proof.
    intros Hlen.
    pose (f:= (λ (a : A)(b : B), (a,b))).
    assert (Hidf: ∀ (l : list A) (k : list B), zip l k = uncurry f <$> zip l k).
    { intros l k. apply list_eq => i.
      rewrite list_lookup_fmap. by destruct (zip l k !! i) as [[??]|]. }
    rewrite {1}Hidf -zip_with_zip zip_with_app //.
  Qed.

  Local Lemma wptp_weak_requisiteness_inv t γb :
    inv nroot (safeInv γb) ⊢
    [∗ list] e ∈ t, (∃ i, i ↪[γb] e) -∗ WP e {{ _, True }}.
  Proof.
    iIntros "#Hinv".
    iLöb as "IH" forall (t).
    iApply (big_sepL_impl (λ _ _, emp)%I); first done.
    iIntros "!#" (? e _) "_ [%tid He◯]".
    destruct (to_val e) as [v|] eqn:He.

    - rewrite -(of_to_val e v); last apply He.
      by iApply wp_value.

    - iApply wp_lift_step_fupd; first done.
      iIntros (σ1 ns κ κs nt) "Hstate_interp".
      (* TODO: is there a way to provide an IntoExist instance under ◇ modality? *)
      iInv nroot as "H" "Hclose1".
      iDestruct (bi.later_exist_except_0 with "H") as ">[%t1 H]".
      iDestruct (bi.later_exist_except_0 with "H") as ">[%σl1 H]".
      iDestruct (bi.later_exist_except_0 with "H") as ">[%nsl H]".
      iDestruct (bi.later_exist_except_0 with "H") as ">[%κl H]".
      iDestruct (bi.later_exist_except_0 with "H") as ">[%ntl H]".
      iDestruct "H" as ">(Hown_state & Ht● & %Hsafe)".
      iApply fupd_mask_intro; first set_solver. iIntros "Hclose2".
      iDestruct (own_state_agree with "Hstate_interp Hown_state") as %Hσlσ.
      iDestruct (ghost_map_lookup with "Ht● He◯") as %Hint1%elem_of_list_to_map_2.

      assert (He_red : reducible e σl1). {
        specialize (Hsafe t1 σl1 e).
        destruct Hsafe as [Hfalse|]; try done.
        - by eapply elem_of_zip_r.
        - rewrite /= He in Hfalse. by inversion Hfalse.
      }

      iSplit; first by iPureIntro; eapply reducible_mono.
      iIntros (e2 σ2 efs Hprim_step) "_ !>!>".

      (* update ghost resources *)
      iMod (ghost_map_update e2 with "Ht● He◯") as "[Ht● He◯]".
      iMod (ghost_map_insert_big (list_to_map (zip (seq (length t1) (length efs)) efs)) with "Ht●") as "[Ht● Hefs◯]".
      { apply map_disjoint_dom.
        rewrite dom_insert_L !dom_list_to_map_L !fst_zip; [|by rewrite length_seq..].
        rewrite !list_to_set_seq.
        assert (tid ∈ (set_seq 0 (length t1) : gset nat)).
        { eapply elem_of_set_seq, elem_of_seq, elem_of_zip_l => //. }
        replace ({[tid]} ∪ set_seq 0 (length t1) : gset nat) with (set_seq 0 (length t1) : gset nat) by set_solver.
        symmetry. apply set_seq_add_disjoint. }
      iAssert ([∗ list] i↦k ∈ efs, (length t1+i) ↪[γb] k)%I with "[Hefs◯]" as "Hefs◯".
      { clear.
        remember (length t1) as len. clear Heqlen.
        iInduction efs as [|ef efs] "IHf" forall (len); first done.
        rewrite big_sepL_cons length_cons -cons_seq zip_cons list_to_map_cons big_sepM_insert; last first.
        { apply not_elem_of_dom_1.
          rewrite dom_list_to_map_L fst_zip; last by rewrite length_seq.
          rewrite list_to_set_seq elem_of_set_seq. lia. }
        rewrite right_id.
        iDestruct "Hefs◯" as "[$ Hefs◯]".
        iDestruct ("IHf" with "Hefs◯") as "Hefs◯".
        iApply (big_sepL_mono with "Hefs◯").
        intros i ??.
        replace (S len + i) with (len + S i) by lia.
        done. }
      edestruct (prim_step_subset) as (σ_ext & σl2 & Hσl1_dis & Hσl2_dis & Heq1 & Heq2 & Hprim_step_l).
      { exact Hσlσ. } { exact He_red. } { exact Hprim_step. }
      subst σ1 σ2.
      iMod (state_update with "Hstate_interp Hown_state") as "[$ Hown_state]".
      { exact Hσl1_dis. } { exact Hσl2_dis. } { exact Hprim_step_l. }

      iMod "Hclose2" as "_".
      iMod ("Hclose1" with "[Ht● $Hown_state]") as "_".
      { (* destruct [t1] into [t1a++e::t1b] *)
        assert (Hlookupt1: t1!!tid = Some e).
        { clear -Hint1.
          assert (lemma: ∀ i, (tid,e) ∈ zip (seq i (length t1)) t1 → i≤tid ∧ t1 !! (tid-i) = Some e).
          { clear. induction t1 as [|e0 t1 IH] => i Hint1; first set_solver.
            rewrite /= elem_of_cons in Hint1. destruct Hint1 as [Hint1|Hint1].
            - simplify_eq. replace (i-i) with 0 by lia. set_solver.
            - destruct (IH _ Hint1) as [Hle Hlookupt1].
              split; first lia.
              apply lookup_cons_Some. right. split; first lia.
              replace (tid-i-1) with (tid - S i) by lia.
              exact Hlookupt1. }
          destruct (lemma 0 Hint1) as [_ H].
          replace (tid-0) with (tid) in H by lia.
          done. }
        destruct (elem_of_list_split_length t1 tid e Hlookupt1) as (t1a & t1b & -> & ->).

        (* update [e] to [e2] *)
        iEval (rewrite [x in seq 0 x]length_app seq_app) in "Ht●".
        iEval (rewrite zip_app; last rewrite length_seq //) in "Ht●".
        iEval (rewrite length_cons -cons_seq zip_cons) in "Ht●".
        assert ((list_to_map (zip (seq 0 (length t1a)) t1a) : gmap nat (expr Λ)) !! length t1a = None).
        { apply not_elem_of_dom_1.
          rewrite dom_list_to_map_L fst_zip; last by rewrite length_seq.
          rewrite list_to_set_seq elem_of_set_seq.
          lia. }
        iEval (rewrite list_to_map_app list_to_map_cons -(insert_union_r _ _ (length t1a) e) //) in "Ht●".
        iEval (rewrite insert_insert) in "Ht●".
        iEval (rewrite (insert_union_r _ _ (length t1a) e2) //) in "Ht●".
        iEval (rewrite -list_to_map_cons -list_to_map_app) in "Ht●".
        iEval (rewrite -zip_cons cons_seq -(length_cons e2)) in "Ht●".
        iEval (rewrite -zip_app; last by apply length_seq) in "Ht●".
        iEval (rewrite -seq_app -[x in seq 0 x]length_app) in "Ht●".

        replace (length (t1a++e::t1b)) with (length (t1a++e2::t1b));
          last rewrite !length_app //.

        (* merge two [list_to_map]s *)
        rewrite map_union_comm; last first.
        { apply map_disjoint_dom.
          rewrite !dom_list_to_map_L !fst_zip; [|by rewrite length_seq..].
          rewrite !list_to_set_seq.
          apply elem_of_disjoint => tid Hin1 Hin2.
          apply elem_of_set_seq in Hin1,Hin2.
          lia. }
        iEval (rewrite -list_to_map_app -zip_app; last by rewrite length_seq) in "Ht●".
        iEval (rewrite -[x in seq x (length efs)](left_id 0 Nat.add (length (t1a++e2::t1b)))) in "Ht●".
        iEval (rewrite -seq_app -length_app) in "Ht●".
        rewrite -assoc -app_comm_cons.

        iFrame "Ht●". iIntros "!>!%".
        intros t3 σ3 e3 _ Hsteps.
        apply Hsafe; first done.
        eapply rtc_l; last exact Hsteps.
        exists κ.
        by apply (step_atomic e σl1 e2 σl2 efs t1a t1b). }

      iModIntro. simpl.
      iAssert (∃ tid, tid ↪[γb] e2)%I with "[$He◯]" as "He◯".
      iDestruct (big_sepL_mono _ (λ _ e, ∃ i, i ↪[γb] e)%I with "Hefs◯") as "Hefs◯".
      { iIntros (???) "$". }
      iCombine "He◯ Hefs◯" as "Ht◯".
      rewrite -(big_sepL_cons (λ _ e, ∃ i, i ↪[γb] e)%I).
      rewrite -(big_sepL_mono (λ _ e, WP e {{_, True}})%I ((λ _ e, WP e {{fork_post}})%I)); last first.
      { intros ???. apply wp_mono =>?. iIntros "_". iApply fork_post_trivial. }
      rewrite -(big_sepL_cons (λ _ e, WP e {{_, True}})%I).
      iApply (big_sepL_wand with "Ht◯").
      iApply "IH".
  Qed.

  Lemma wptp_weak_requisiteness t P :
    (∀ σ, P σ → safe_tp NotStuck t σ) →
    ⌞P⌟ ⊢ |={⊤}=> [∗ list] e ∈ t, WP e {{ _, True }}.
  Proof.
    iIntros (Hsafe) "HP".
    iDestruct "HP" as (σl nsl κsl ntl) "[Hown_state %HP]".
    specialize (Hsafe σl HP).
    iMod (ghost_map_alloc (list_to_map (zip (seq 0 (length t)) t))) as (γb) "[Ht● Ht◯]".
    iAssert ([∗ list] k ∈ t, ∃ i, i ↪[γb] k)%I with "[Ht◯]" as "Ht◯".
    { clear.
      remember 0 as start. clear Heqstart.
      iInduction t as [|e t] "IH" forall (start); first done.
      rewrite big_sepL_cons length_cons -cons_seq zip_cons list_to_map_cons big_sepM_insert; last first.
      { apply not_elem_of_dom_1.
        rewrite dom_list_to_map_L fst_zip; last by rewrite length_seq.
        rewrite list_to_set_seq elem_of_set_seq. lia. }
      iDestruct "Ht◯" as "[$ Ht◯]".
      by iApply "IH". }
    iMod (inv_alloc nroot ⊤ (safeInv γb) with "[$Hown_state $Ht● //]") as "#Hinv".
    iModIntro.
    iApply (big_sepL_wand with "Ht◯").
    by iApply wptp_weak_requisiteness_inv.
  Qed.

  Lemma wp_requisiteness_nofork e P Q :
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
      iApply (fupd_mask_mono ∅); first set_solver.
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

  Lemma hoare_requisiteness_nofork e P Q :
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
    iApply (fupd_mask_mono ∅); first set_solver.
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
  Lemma wptp_requisiteness e t P Q :
    (∀ σ, P σ → adequate_tp NotStuck (e::t) σ Q) →
    ⌞P⌟ ⊢ |={⊤}=> WP e {{ v, ⌞Q v⌟ }} ∗ [∗ list] e ∈ t, WP e {{ _, True }}.
  Abort.
End requisiteness.
