From iris.proofmode Require Import base ltac_tactics.
From iris.base_logic Require Import ghost_map invariants.
From iris.program_logic Require Export lifting.
From complete_iris.program_logic Require Export adequacy.

Class coirisG_gen (hlc : has_lc) (Λ : language) (Σ: gFunctors) `{!irisGS_gen hlc Λ Σ} := CoirisG {
  substate : relation (state Λ);
  state_empty : state Λ;
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

  own_state_empty ns κs nt : ⊢ own_state state_empty ns κs nt;

  own_state_agree σ ns κs nt σ' ns' κs' nt' :
    state_interp σ ns κs nt -∗ own_state σ' ns' κs' nt' -∗ ⌜substate σ' σ⌝;

  state_update e e' σ σ' σ_ext ns ns' κ κs κ' nt nt' efs :
    state_disjoint σ σ_ext → state_disjoint σ' σ_ext → prim_step e σ κ e' σ' efs →
    state_interp (state_union σ σ_ext) ns (κ++κs) nt -∗ own_state σ ns' κ' nt' ={∅}=∗
    state_interp (state_union σ' σ_ext) (S ns) κs (length efs + nt) ∗ own_state σ' (S ns) κs (length efs + nt);
}.
Global Arguments CoirisG {hlc Λ Σ _}.

Notation coirisG Λ Σ := (coirisG_gen HasLc Λ Σ).

Definition bi_state `{!irisGS_gen hlc Λ Σ, !coirisG_gen hlc Λ Σ} (P : state Λ → Prop) : iProp Σ :=
  ∃ σ ns κs nt, own_state σ ns κs nt ∗ ⌜P σ⌝.
Global Arguments bi_state {_ _ _ _ _} _%_stdpp_scope.
Notation "⌞ P ⌟" := (bi_state P) (format "⌞ P ⌟") : bi_scope.

Section stateful.
  Context `{!irisGS_gen hlc Λ Σ, !coirisG_gen hlc Λ Σ}.

  Lemma bi_pure_state' (P : Prop) :
    P → ⊢ ⌞ λ _, P ⌟.
  Proof.
    iIntros (HP).
    iExists state_empty,0,[],0. iSplit; last done.
    iApply own_state_empty.
  Qed.

  Lemma bi_pure_state (P : Prop) :
    ⌜P⌝ ⊢ ⌞ λ _, P ⌟.
  Proof. by iIntros "%HP"; iApply bi_pure_state'. Qed.
End stateful.

Class requisiteG Λ Σ := RequisiteG {
  #[local] requisiteG_bag :: ghost_mapG Σ nat (expr Λ * (val Λ → Prop));
}.

Definition requisiteΣ Λ := #[ghost_mapΣ nat (expr Λ * (val Λ → Prop))].

Global Instance subG_requisiteG Λ Σ :
  subG (requisiteΣ Λ) Σ → requisiteG Λ Σ.
Proof. solve_inG. Qed.

Section requisiteness.
  Context `{!irisGS_gen hlc Λ Σ, !coirisG_gen hlc Λ Σ, !requisiteG Λ Σ}.

  Implicit Types (e : expr Λ) (v : val Λ) (σ : state Λ) (t : list (expr Λ)) (Q : (val Λ) → (state Λ) → Prop).

  Local Instance into_val_val v : IntoVal (of_val v) v.
  Proof. done. Qed.

  Definition add_postcond (φ : val Λ → Prop) (t : list (expr Λ)) :=
    zip t (φ :: repeat (λ _, True) (length t - 1)).

  Definition requisiteInv φ γb : iProp Σ :=
    ∃ t2 σl nsl κsl ntl, own_state σl nsl κsl ntl ∗
      ghost_map_auth γb 1 (list_to_map (zip (seq 0 (length t2)) (add_postcond φ t2))) ∗
      ⌜adequate_tp NotStuck t2 σl (λ v _, φ v)⌝.

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
  Local Lemma repeat_S {A} (a : A) n :
    repeat a (S n) = a::repeat a n.
  Proof. done. Qed.

  Local Lemma wptp_requisiteness_inv (tφ : list (expr Λ * (val Λ → Prop))) φ₀ γb :
    inv nroot (requisiteInv φ₀ γb) ⊢
    [∗ list] eφ ∈ tφ, (∃ i, i ↪[γb] eφ) -∗ let '(e,φ) := eφ in WP e {{ v, ⌜φ v⌝ }}.
  Proof.
    pose (Truep := λ _ : val Λ, True).
    iIntros "#Hinv".
    iLöb as "IH" forall (tφ).
    iApply (big_sepL_impl (λ _ _, emp)%I); first done.
    iIntros "!#" (? [e φ] _) "_ [%tid He◯]".
    destruct (to_val e) as [v|] eqn:He.

    - rewrite -(of_to_val e v); last apply He.
      iApply wp_value_fupd.
      iInv nroot as "H" "Hclose".
      (* TODO: is there a way to provide an IntoExist instance under ◇ modality? *)
      iDestruct (bi.later_exist_except_0 with "H") as ">[%t1 H]".
      iDestruct (bi.later_exist_except_0 with "H") as ">[%σl1 H]".
      iDestruct (bi.later_exist_except_0 with "H") as ">[%nsl H]".
      iDestruct (bi.later_exist_except_0 with "H") as ">[%κl H]".
      iDestruct (bi.later_exist_except_0 with "H") as ">[%ntl H]".
      iDestruct "H" as ">(Hown_state & Ht● & %Hadq)".
      iDestruct (ghost_map_lookup with "Ht● He◯") as %Hint1%elem_of_list_to_map_2%elem_of_zip_r.
      iMod ("Hclose" with "[$Hown_state $Ht● //]") as "_".
      iPureIntro.
      destruct Hadq.
      destruct t1 as [|e1 t1]; first done.
      rewrite /add_postcond zip_cons length_cons elem_of_cons in Hint1.
      replace (S (length t1) -1) with (length t1) in Hint1 by lia.
      destruct Hint1 as [Hmain_thread | Hint1].
      + simplify_eq. eapply adequate_tp_result, rtc_refl.
      + apply elem_of_zip_r, list_elem_of_In, repeat_spec in Hint1.
        rewrite Hint1 //.

    - iApply wp_lift_step_fupd; first done.
      iIntros (σ1 ns κ κs nt) "Hstate_interp".
      iInv nroot as "H" "Hclose1".
      iDestruct (bi.later_exist_except_0 with "H") as ">[%t1 H]".
      iDestruct (bi.later_exist_except_0 with "H") as ">[%σl1 H]".
      iDestruct (bi.later_exist_except_0 with "H") as ">[%nsl H]".
      iDestruct (bi.later_exist_except_0 with "H") as ">[%κl H]".
      iDestruct (bi.later_exist_except_0 with "H") as ">[%ntl H]".
      iDestruct "H" as ">(Hown_state & Ht● & %Hadq)".
      iApply fupd_mask_intro; first set_solver. iIntros "Hclose2".
      iDestruct (own_state_agree with "Hstate_interp Hown_state") as %Hσlσ.
      iDestruct (ghost_map_lookup with "Ht● He◯") as %Hint1%elem_of_list_to_map_2.

      assert (He_red : reducible e σl1). {
        destruct Hadq.
        specialize (adequate_tp_not_stuck t1 σl1 e eq_refl (ltac:(apply rtc_refl))).
        destruct adequate_tp_not_stuck as [Hfalse|]; try done.
        - by eapply elem_of_zip_l,elem_of_zip_r.
        - rewrite /= He in Hfalse. by inversion Hfalse.
      }

      iSplit; first by iPureIntro; eapply reducible_mono.
      iIntros (e2 σ2 efs Hprim_step) "_ !>!>".

      (* update ghost resources *)
      iMod (ghost_map_update (e2, φ) with "Ht● He◯") as "[Ht● He◯]".
      iMod (ghost_map_insert_big (list_to_map (zip (seq (length t1) (length efs)) (zip efs (repeat Truep (length efs))))) with "Ht●") as "[Ht● Hefs◯]".
      { apply map_disjoint_dom.
        rewrite dom_insert_L !dom_list_to_map_L !fst_zip; first last.
        { rewrite length_seq length_zip repeat_length. lia. }
        { rewrite length_seq length_zip length_cons repeat_length. lia. }
        rewrite !list_to_set_seq.
        assert (tid ∈ (set_seq 0 (length t1) : gset nat)).
        { eapply elem_of_set_seq, elem_of_seq, elem_of_zip_l => //. }
        replace ({[tid]} ∪ set_seq 0 (length t1) : gset nat) with (set_seq 0 (length t1) : gset nat) by set_solver.
        symmetry. apply set_seq_add_disjoint. }
      iAssert ([∗ list] i↦'(k,φ) ∈ (zip efs (repeat Truep (length efs))), (length t1+i) ↪[γb] (k,φ))%I with "[Hefs◯]" as "Hefs◯".
      { clear.
        remember (length t1) as len. clear Heqlen.
        iInduction efs as [|ef efs] "IHf" forall (len); first done.
        rewrite length_cons repeat_S zip_cons big_sepL_cons.
        rewrite -cons_seq zip_cons list_to_map_cons big_sepM_insert; last first.
        { apply not_elem_of_dom_1.
          rewrite dom_list_to_map_L fst_zip.
          - rewrite list_to_set_seq elem_of_set_seq. lia.
          - rewrite length_seq length_zip repeat_length. lia. }
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
        assert (Hlen_add_postcond_φ₀_t1: length t1 = length (add_postcond φ₀ t1)).
        { destruct t1; first set_solver.
          rewrite /add_postcond zip_cons !length_cons length_zip repeat_length. lia. }
        rewrite Hlen_add_postcond_φ₀_t1 in Hint1.
        rewrite Hlen_add_postcond_φ₀_t1.
        remember (add_postcond φ₀ t1) as t1φ.
        assert (Hlookupt1φ: t1φ!!tid = Some (e,φ)).
        { clear -Hint1.
          assert (lemma: ∀ i, (tid,(e,φ)) ∈ zip (seq i (length t1φ)) t1φ → i≤tid ∧ t1φ !! (tid-i) = Some (e,φ)).
          { clear. induction t1φ as [|e0 t1φ IH] => i Hint1; first set_solver.
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
        destruct (list_elem_of_split_length t1φ tid (e,φ) Hlookupt1φ) as (t1φa & t1φb & -> & ->).

        (* update [e] to [e2] *)
        replace (<[length t1φa:=(e2, φ)]> (
          list_to_map (zip (seq 0 (length (t1φa ++ (e,φ) :: t1φb)))
          (t1φa ++ (e,φ) :: t1φb))))
          with (list_to_map (zip (seq 0 (length (t1φa ++ (e2,φ) :: t1φb)))
          (t1φa ++ (e2,φ) :: t1φb)) : gmap _ _); last first.
        { rewrite !length_app !seq_app.
          rewrite !zip_app; [|by rewrite length_seq..].
          rewrite !length_cons -!cons_seq !zip_cons.
          assert ((list_to_map (zip (seq 0 (length t1φa)) t1φa) : gmap _ _) !! length t1φa = None).
          { apply not_elem_of_dom_1.
            rewrite dom_list_to_map_L fst_zip; last by rewrite length_seq.
            rewrite list_to_set_seq elem_of_set_seq.
            lia. }
          rewrite !list_to_map_app !list_to_map_cons -!insert_union_r //.
          rewrite insert_insert_eq //. }

        replace (length (t1φa++(e,φ)::t1φb)) with (length (t1φa++(e2,φ)::t1φb));
          last rewrite !length_app //.

        (* merge two [list_to_map]s *)
        rewrite map_union_comm; last first.
        { apply map_disjoint_dom.
          rewrite !dom_list_to_map_L !fst_zip; first last.
          { rewrite length_seq length_zip repeat_length. lia. }
          { rewrite length_seq. lia. }
          rewrite !list_to_set_seq.
          apply elem_of_disjoint => tid Hin1 Hin2.
          apply elem_of_set_seq in Hin1,Hin2.
          lia. }
        iEval (rewrite -list_to_map_app -zip_app; last by rewrite length_seq) in "Ht●".
        iEval (rewrite -seq_app) in "Ht●".
        replace (length (t1φa ++ (e2, φ) :: t1φb) + length efs)
          with (length (t1φa.*1++e2::t1φb.*1++efs)); last first.
        { rewrite !length_app !length_cons length_app !length_fmap. lia. }
        replace ((t1φa ++ (e2, φ) :: t1φb) ++ zip efs (repeat Truep (length efs)))
          with (add_postcond φ₀ (t1φa.*1++e2::t1φb.*1++efs)); last first.
        { rewrite /add_postcond in Heqt1φ.
          apply (f_equal (λ x, x.*2)) in Heqt1φ.
          rewrite snd_zip in Heqt1φ; last first.
          { destruct t1.
            - rewrite length_nil length_app length_cons in Hlen_add_postcond_φ₀_t1.
              lia.
            - rewrite !length_cons repeat_length. lia. }
          rewrite fmap_app fmap_cons /= in Heqt1φ.
          rewrite /add_postcond.
          replace (length (t1φa.*1 ++ e2 :: t1φb.*1 ++ efs) - 1)
            with (length t1 - 1 + length efs); last first.
          { rewrite Hlen_add_postcond_φ₀_t1.
            rewrite !length_app !length_cons length_app !length_fmap. lia. }
          rewrite repeat_app [x in zip _ x]app_comm_cons -Heqt1φ.
          rewrite [in x in zip x _]app_comm_cons assoc zip_app;
            last by rewrite !length_app !length_cons !length_fmap.
          f_equal.
          rewrite -[x in _ = x]zip_fst_snd !fmap_app !fmap_cons //. }

        iFrame "Ht●". iIntros "!>!%".
        rewrite /add_postcond in Heqt1φ.
        apply (f_equal (λ x, x.*1)) in Heqt1φ.
        rewrite fst_zip in Heqt1φ; last (rewrite length_cons repeat_length; lia).
        rewrite fmap_app fmap_cons /= in Heqt1φ.
        rewrite -Heqt1φ in Hadq.
        eapply adequate_tp_erased_step; last exact Hadq.
        exists κ. by eapply step_atomic. }

      iModIntro.
      iAssert (∃ tid, tid ↪[γb] (e2, φ))%I with "[$He◯]" as "He◯".
      iDestruct (big_sepL_mono _ (λ _ eφ, ∃ i, i ↪[γb] eφ)%I with "Hefs◯") as "Hefs◯".
      { iIntros (? [? ?] ?) "$". }
      iCombine "He◯ Hefs◯" as "Ht◯".
      rewrite -(big_sepL_cons (λ _ eφ, ∃ i, i ↪[γb] eφ)%I).
      pose (f:=(λ e, (e,Truep))).
      replace (zip efs (repeat Truep (length efs))) with (f <$> efs); last first.
      { clear. induction efs; first done.
        rewrite fmap_cons length_cons repeat_S zip_cons. f_equal. assumption. }
      pose (Φ := (λ (_ : nat) '(e,φ), WP e {{v, ⌜φ v⌝}})%I).
      rewrite -(big_sepL_mono (λ i e, Φ i (f e))%I ((λ _ e, WP e {{fork_post}})%I)); last first.
      { intros ???. apply wp_mono =>?. iIntros "_". iApply fork_post_trivial. }
      rewrite -(big_sepL_fmap f Φ). rewrite /Φ /f.
      rewrite -(big_sepL_cons Φ (e2,φ)).
      iApply (big_sepL_wand with "Ht◯"). rewrite /Φ.
      iApply "IH".
  Qed.

  Lemma wptp_requisiteness e t P φ :
    (∀ σ, P σ → adequate_tp NotStuck (e::t) σ (λ v _, φ v)) →
    ⌞P⌟ ⊢ |={⊤}=> WP e {{ v, ⌜φ v⌝ }} ∗ [∗ list] e ∈ t, WP e {{ _, True }}.
  Proof.
    iIntros (Hadq) "HP".
    iDestruct "HP" as (σl nsl κsl ntl) "[Hown_state %HP]".
    specialize (Hadq σl HP).
    iMod (ghost_map_alloc (list_to_map (zip (seq 0 (length (e::t))) (add_postcond φ (e::t))))) as (γb) "[Ht● Ht◯]".
    iAssert ([∗ list] k ∈ add_postcond φ (e::t), ∃ i, i ↪[γb] k)%I with "[Ht◯]" as "Ht◯".
    { clear.
      remember 0 as start. clear Heqstart.
      replace (length (e::t)) with (length (add_postcond φ (e::t))); last first.
      { rewrite /add_postcond zip_cons !length_cons length_zip repeat_length. lia. }
      remember (add_postcond φ (e::t)) as tφ. clear Heqtφ.
      iInduction tφ as [|eφ tφ] "IH" forall (start); first done.
      rewrite big_sepL_cons length_cons -cons_seq zip_cons list_to_map_cons big_sepM_insert; last first.
      { apply not_elem_of_dom_1.
        rewrite dom_list_to_map_L fst_zip; last by rewrite length_seq.
        rewrite list_to_set_seq elem_of_set_seq. lia. }
      iDestruct "Ht◯" as "[$ Ht◯]".
      by iApply "IH". }
    iMod (inv_alloc nroot ⊤ (requisiteInv φ γb) with "[$Hown_state $Ht● //]") as "#Hinv".

    iModIntro.
    pose (f:=(λ e, (e, λ v, True))).
    rewrite /add_postcond zip_cons.
    replace (zip t (repeat (λ v, True) (length (e::t) - 1))) with (f <$> t); last first.
    { clear.
      replace (length (e::t)-1) with (length t) by (rewrite length_cons; lia).
      induction t; first done.
      rewrite fmap_cons length_cons repeat_S zip_cons. f_equal. assumption. }
    pose (Φ := (λ (_ : nat) '(e,φ), WP e {{v, ⌜φ v⌝}})%I).
    rewrite -(big_sepL_mono (λ i e, Φ i (f e))%I ((λ _ e, WP e {{_, True}})%I)); last first.
    { intros ???. apply wp_mono =>? //. }
    rewrite -(big_sepL_fmap f Φ). rewrite /Φ /f.
    rewrite -(big_sepL_cons Φ (e,φ)). rewrite /Φ.
    iApply (big_sepL_wand with "Ht◯").
    by iApply wptp_requisiteness_inv.
  Qed.

  Lemma wp_requisiteness e P φ :
    (∀ σ, P σ → adequate NotStuck e σ (λ v _, φ v)) →
    ⌞P⌟ ⊢ WP e {{ v, ⌜φ v⌝ }}.
  Proof.
    iIntros (Hadq) "HP".
    iMod (wptp_requisiteness e [] with "HP") as "[$ _]".
    intros σ HP. apply adequate_tp_adequate. auto.
  Qed.

  Lemma wp_requisiteness_nopre e φ :
    (∀ σ, adequate NotStuck e σ (λ v _, φ v)) →
    ⊢ WP e {{ v, ⌜φ v⌝ }}.
  Proof.
    iIntros (Hadq).
    iApply (wp_requisiteness e (λ _, True)); first by auto.
    by iApply bi_pure_state.
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
End requisiteness.
