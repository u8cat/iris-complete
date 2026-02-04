From iris.proofmode Require Import base ltac_tactics.
From complete_iris.program_logic Require Export requisiteness.
From iris.heap_lang Require Export proofmode notation.

Module colang.
Global Instance state_empty : Empty state :=
  {| heap := ∅; used_proph_id := ∅ |}.

Global Instance substate : SubsetEq state := λ σ1 σ2,
  σ1.(heap) ⊆ σ2.(heap) ∧ σ1.(used_proph_id) ⊆ σ2.(used_proph_id).

Global Instance state_disjoint : Disjoint state := λ σ1 σ2,
  σ1.(heap) ##ₘ σ2.(heap) ∧ σ1.(used_proph_id) ## σ2.(used_proph_id).

Global Instance state_union : Union state := λ σ1 σ2,
  {| heap := σ1.(heap) ∪ σ2.(heap); used_proph_id := σ1.(used_proph_id) ∪ σ2.(used_proph_id) |}.

Global Instance state_difference : Difference state := λ σ1 σ2,
  {| heap := σ1.(heap)∖σ2.(heap); used_proph_id := σ1.(used_proph_id)∖σ2.(used_proph_id) |}.

Global Instance substate_preorder : PreOrder (⊆@{state}).
Proof.
  constructor.
  - intros [h p]. rewrite /subseteq /substate //.
  - intros [h1 p1] [h2 p2] [h3 p3]. rewrite /subseteq /substate /=.
    intros [Hh12 Hp12] [Hh23 Hp23]. split; by etrans.
Qed.

Global Instance state_empty_left_id : LeftId (=@{state}) ∅ (∪).
Proof.
  intros [h p]. rewrite /union /state_union /= left_id.
  f_equal. set_solver.
Qed.

Global Instance state_empty_right_id : RightId (=@{state}) ∅ (∪).
Proof.
  intros [h p]. rewrite /union /state_union /= right_id.
  f_equal. set_solver.
Qed.

Lemma state_disjoint_difference_r1 (σ0 σ1 σ2 : state) :
  σ0 ⊆ σ2 → σ0 ## σ1∖σ2.
Proof.
  intros [Hsubseth%subseteq_dom Hsubsetp].
  split; first apply map_disjoint_dom; set_solver.
Qed.

Lemma state_disjoint_difference_l1 (σ1 σ2 σ0 : state) :
  σ0 ⊆ σ2 → σ1∖σ2 ## σ0.
Proof.
  intros [Hsubseth%subseteq_dom Hsubsetp].
  split; first apply map_disjoint_dom; set_solver.
Qed.

Lemma state_union_difference (σ1 σ2 : state) :
  σ1 ⊆ σ2 → σ2 = σ1 ∪ σ2∖σ1.
Proof.
  destruct σ1 as [h1 p1]. destruct σ2 as [h2 p2].
  intros [Hsubseth Hsubsetp]. simpl in Hsubseth, Hsubsetp.
  rewrite /union /difference /state_union /state_difference /=.
  f_equal.
  - rewrite map_difference_union //.
  - rewrite -union_difference_L //.
Qed.

Lemma state_union_comm (σ1 σ2 : state) :
  σ1 ## σ2 → σ1 ∪ σ2 = σ2 ∪ σ1.
Proof.
  intros [Hdisjm Hdisjp].
  destruct σ1, σ2. rewrite /union /state_union /=.
  f_equal.
  - by apply map_union_comm.
  - apply: comm.
Qed.

Local Lemma heap_difference_difference_r (h1 h2 : gmap loc (option val)) :
  h2 ⊆ h1 → (h1 ∖ (h1 ∖ h2)) = h2.
Proof.
  intros Hsubseth.
  rewrite map_subseteq_spec in Hsubseth.
  apply map_eq => l.
  rewrite !lookup_difference.
  destruct (h2!!l) as [h2l|] eqn:Hlookup2; first auto.
  destruct (h1!!l) as [h1l|] eqn:Hlookup1; auto.
Qed.

Lemma state_difference_difference_r (σ1 σ2 : state) :
  σ2 ⊆ σ1 → (σ1 ∖ (σ1 ∖ σ2)) = σ2.
Proof.
  destruct σ1 as [h1 p1]. destruct σ2 as [h2 p2].
  intros [Hsubseth Hsubsetp]. simpl in Hsubseth, Hsubsetp.
  rewrite /difference /state_difference /=.
  f_equal.
  - by apply heap_difference_difference_r.
  - rewrite difference_difference_r_L.
    set_solver.
Qed.

Lemma state_subseteq_difference_l (σ1 σ2 σ0 : state) :
  σ1 ⊆ σ0 → σ1∖σ2 ⊆ σ0.
Proof.
  destruct σ1, σ2, σ0.
  rewrite /subseteq /substate /difference /state_difference /=.
  intros [??]. split.
  - by apply map_subseteq_difference_l.
  - set_solver.
Qed.

Section substate.
  Implicit Types (e : expr) (σ : state) (κ κs : list observation) (efs : list expr).

  Local Lemma atomic_reducible_mono e σ σ' κ v σ2 efs : σ ⊆ σ' →
    base_step e σ κ (Val v) σ2 efs →
    (∃ κ v σ2, base_step e σ' κ (Val v) σ2 efs).
  Proof.
    intros [Hsubheap Hsubproph] Hbase_step.
    remember (Val v) as e2.
    induction Hbase_step; simplify_eq; try solve [do 3 eexists; econstructor; eauto using lookup_weaken].
    - do 3 eexists; econstructor; eauto.
      intros i Hi1 Hi2. apply not_elem_of_dom_1, Loc.fresh_fresh. done.
    - do 3 eexists; econstructor; eauto. apply is_fresh.
    - destruct (IHHbase_step Hsubheap Hsubproph eq_refl) as (κ & v2 & σ2 & Hbase_step').
      do 3 eexists; econstructor; eauto.
  Qed.

  Lemma reducible_mono e σ σ' : σ ⊆ σ' → reducible e σ → reducible e σ'.
  Proof.
    intros [Hsubheap Hsubproph] Hred.
    destruct Hred as (κ & e2 & σ2 & efs & Hprim_step). simpl in *.
    destruct Hprim_step as [K e_ e2_ -> -> Hbase_step]. simpl in *.
    destruct Hbase_step; try solve [do 4 eexists; econstructor; eauto; econstructor; eauto using lookup_weaken].
    - do 4 eexists; econstructor; eauto; econstructor; eauto.
      intros i Hi1 Hi2. apply not_elem_of_dom_1, Loc.fresh_fresh. done.
    - do 4 eexists; econstructor; eauto; econstructor. apply is_fresh.
    - apply (atomic_reducible_mono _ _ σ') in Hbase_step as (κ & v' & σ2 & Hbase_step'); last done.
      do 4 eexists; econstructor; eauto; econstructor; eauto.
  Qed.

  Local Lemma reducible_free_loc K l σ :
    reducible (fill K (Free (Val (LitV (LitLoc l))))) σ →
    ∃ v, σ.(heap) !! l = Some (Some v).
  Proof.
    intros Hred%reducible_fill_inv; last done.
    destruct Hred as (κ & e2 & σ2 & efs & Hprim_step).
    destruct Hprim_step as [K' e_ e2_ Heq -> Hbase_step].
    simpl in *.
    induction K' as [|k' K' _] using rev_ind.
    - simpl in Heq. subst e_.
      inversion Hbase_step. eauto.
    - rewrite fill_app /= in Heq.
      destruct k'; simpl in Heq; try discriminate Heq.
      injection Heq as Heq.
      apply (f_equal to_val), eq_sym in Heq.
      simpl in Heq.
      apply to_val_fill_some in Heq as [-> ->].
      apply val_base_stuck in Hbase_step.
      simpl in Hbase_step.
      discriminate Hbase_step.
  Qed.

  Local Lemma reducible_load_loc K l σ :
    reducible (fill K (Load (Val (LitV (LitLoc l))))) σ →
    ∃ v, σ.(heap) !! l = Some (Some v).
  Proof.
    intros Hred%reducible_fill_inv; last done.
    destruct Hred as (κ & e2 & σ2 & efs & Hprim_step).
    destruct Hprim_step as [K' e_ e2_ Heq -> Hbase_step].
    simpl in *.
    induction K' as [|k' K' _] using rev_ind.
    - simpl in Heq. subst e_.
      inversion Hbase_step. eauto.
    - rewrite fill_app /= in Heq.
      destruct k'; simpl in Heq; try discriminate Heq.
      injection Heq as Heq.
      apply (f_equal to_val), eq_sym in Heq.
      simpl in Heq.
      apply to_val_fill_some in Heq as [-> ->].
      apply val_base_stuck in Hbase_step.
      simpl in Hbase_step.
      discriminate Hbase_step.
  Qed.

  Local Lemma reducible_store_loc K l w σ :
    reducible (fill K (Store (Val (LitV (LitLoc l))) (Val w))) σ →
    ∃ v, σ.(heap) !! l = Some (Some v).
  Proof.
    intros Hred%reducible_fill_inv; last done.
    destruct Hred as (κ & e2 & σ2 & efs & Hprim_step).
    destruct Hprim_step as [K' e_ e2_ Heq -> Hbase_step].
    simpl in *.
    induction K' as [|k' K' _] using rev_ind.
    - simpl in Heq. subst e_.
      inversion Hbase_step. eauto.
    - rewrite fill_app /= in Heq.
      destruct k'; simpl in Heq; try discriminate Heq.
      + injection Heq as Heq.
        apply (f_equal to_val), eq_sym in Heq.
        simpl in Heq.
        apply to_val_fill_some in Heq as [-> ->].
        apply val_base_stuck in Hbase_step.
        simpl in Hbase_step.
        discriminate Hbase_step.
      + injection Heq as ? Heq.
        apply (f_equal to_val), eq_sym in Heq.
        simpl in Heq.
        apply to_val_fill_some in Heq as [-> ->].
        apply val_base_stuck in Hbase_step.
        simpl in Hbase_step.
        discriminate Hbase_step.
  Qed.

  Local Lemma reducible_xchg_loc K l v2 σ :
    reducible (fill K (Xchg (Val (LitV (LitLoc l))) (Val v2))) σ →
    ∃ v, σ.(heap) !! l = Some (Some v).
  Proof.
    intros Hred%reducible_fill_inv; last done.
    destruct Hred as (κ & e2 & σ2 & efs & Hprim_step).
    destruct Hprim_step as [K' e_ e2_ Heq -> Hbase_step].
    simpl in *.
    induction K' as [|k' K' _] using rev_ind.
    - simpl in Heq. subst e_.
      inversion Hbase_step. eauto.
    - rewrite fill_app /= in Heq.
      destruct k'; simpl in Heq; try discriminate Heq.
      + injection Heq as Heq.
        apply (f_equal to_val), eq_sym in Heq.
        simpl in Heq.
        apply to_val_fill_some in Heq as [-> ->].
        apply val_base_stuck in Hbase_step.
        simpl in Hbase_step.
        discriminate Hbase_step.
      + injection Heq as ? Heq.
        apply (f_equal to_val), eq_sym in Heq.
        simpl in Heq.
        apply to_val_fill_some in Heq as [-> ->].
        apply val_base_stuck in Hbase_step.
        simpl in Hbase_step.
        discriminate Hbase_step.
  Qed.

  Local Lemma reducible_cmpxchg_loc K l v1 v2 σ :
    reducible (fill K (CmpXchg (Val (LitV (LitLoc l))) (Val v1) (Val v2))) σ →
    ∃ v, σ.(heap) !! l = Some (Some v).
  Proof.
    intros Hred%reducible_fill_inv; last done.
    destruct Hred as (κ & e2 & σ2 & efs & Hprim_step).
    destruct Hprim_step as [K' e_ e2_ Heq -> Hbase_step].
    simpl in *.
    induction K' as [|k' K' _] using rev_ind.
    - simpl in Heq. subst e_.
      inversion Hbase_step. eauto.
    - rewrite fill_app /= in Heq.
      destruct k'; simpl in Heq; try discriminate Heq.
      + injection Heq as Heq.
        apply (f_equal to_val), eq_sym in Heq.
        simpl in Heq.
        apply to_val_fill_some in Heq as [-> ->].
        apply val_base_stuck in Hbase_step.
        simpl in Hbase_step.
        discriminate Hbase_step.
      + injection Heq as ? Heq.
        apply (f_equal to_val), eq_sym in Heq.
        simpl in Heq.
        apply to_val_fill_some in Heq as [-> ->].
        apply val_base_stuck in Hbase_step.
        simpl in Hbase_step.
        discriminate Hbase_step.
      + injection Heq as ?? Heq.
        apply (f_equal to_val), eq_sym in Heq.
        simpl in Heq.
        apply to_val_fill_some in Heq as [-> ->].
        apply val_base_stuck in Hbase_step.
        simpl in Hbase_step.
        discriminate Hbase_step.
  Qed.

  Local Lemma reducible_faa_loc K l i2 σ :
    reducible (fill K (FAA (Val (LitV (LitLoc l))) (Val (LitV (LitInt i2))))) σ →
    ∃ i1, σ.(heap) !! l = Some (Some (LitV (LitInt i1))).
  Proof.
    intros Hred%reducible_fill_inv; last done.
    destruct Hred as (κ & e2 & σ2 & efs & Hprim_step).
    destruct Hprim_step as [K' e_ e2_ Heq -> Hbase_step].
    simpl in *.
    induction K' as [|k' K' _] using rev_ind.
    - simpl in Heq. subst e_.
      inversion Hbase_step. eauto.
    - rewrite fill_app /= in Heq.
      destruct k'; simpl in Heq; try discriminate Heq.
      + injection Heq as Heq.
        apply (f_equal to_val), eq_sym in Heq.
        simpl in Heq.
        apply to_val_fill_some in Heq as [-> ->].
        apply val_base_stuck in Hbase_step.
        simpl in Hbase_step.
        discriminate Hbase_step.
      + injection Heq as ? Heq.
        apply (f_equal to_val), eq_sym in Heq.
        simpl in Heq.
        apply to_val_fill_some in Heq as [-> ->].
        apply val_base_stuck in Hbase_step.
        simpl in Hbase_step.
        discriminate Hbase_step.
  Qed.

  Local Lemma reducible_resolve_red K e p w σ σl κ v σ' efs :
    base_step e σ κ (Val v) σ' efs →
    reducible (fill K (Resolve e (Val (LitV (LitProphecy p))) (Val w))) σl →
    p ∈ σl.(used_proph_id) ∧ ∃ κl vl σl' efsl, base_step e σl κl (Val vl) σl' efsl.
  Proof.
    intros Hatomic Hred%reducible_fill_inv; last done.
    destruct Hred as (? & e2 & σ2 & ? & Hprim_step).
    destruct Hprim_step as [K' e_ e2_ Heq -> Hbase_step].
    simpl in *.
    induction K' as [|k' K' _] using rev_ind.
    - simpl in Heq. subst e_.
      inversion Hbase_step. eauto 6.
    - rewrite fill_app /= in Heq.
      destruct k'; simpl in Heq; try discriminate Heq.
      + injection Heq as ->.
        apply base_ctx_step_val in Hatomic as [? Heq].
        apply to_val_fill_some in Heq as [-> ->].
        apply val_base_stuck in Hbase_step.
        simpl in Hbase_step.
        discriminate Hbase_step.
      + injection Heq as ? Heq.
        apply (f_equal to_val), eq_sym in Heq.
        simpl in Heq.
        apply to_val_fill_some in Heq as [-> ->].
        apply val_base_stuck in Hbase_step.
        simpl in Hbase_step.
        discriminate Hbase_step.
      + injection Heq as ?? Heq.
        apply (f_equal to_val), eq_sym in Heq.
        simpl in Heq.
        apply to_val_fill_some in Heq as [-> ->].
        apply val_base_stuck in Hbase_step.
        simpl in Hbase_step.
        discriminate Hbase_step.
  Qed.

  Local Lemma state_init_heap_subseteq l n v σ :
    (0 < n)%Z →
    (∀ i : Z, (0 ≤ i)%Z → (i < n)%Z → heap σ !! (l +ₗ i) = None) →
    σ ⊆ state_init_heap l n v σ.
  Proof.
    intros Hn Hfresh. destruct σ as [h p].
    rewrite /state_init_heap /subseteq /substate.
    simpl in *. split; last done.
    apply map_union_subseteq_r.
    apply heap_array_map_disjoint.
    rewrite length_replicate Z2Nat.id; [done|lia].
  Qed.

  Local Lemma subseteq_heap_update_local (σ σl : state) l v :
    σl ⊆ σ → is_Some (heap σl !! l) →
    σ ∖ σl ⊆ state_upd_heap <[l:=v]> σ.
  Proof.
    destruct σ as [h ?], σl as [hl ?].
    rewrite /subseteq /substate /=.
    intros [Hsubset ?] HisSome. split; last set_solver.
    clear - Hsubset HisSome.
    apply map_subseteq_spec => l' v' Hlookup.
    rewrite lookup_difference in Hlookup.
    destruct HisSome as [? Hhl_l'].
    destruct (decide (l = l')) as [<- | Hne].
    - rewrite Hhl_l' in Hlookup. discriminate Hlookup.
    - rewrite lookup_insert_ne //.
      destruct (hl!!l'); done.
  Qed.

  Local Lemma subseteq_used_proph_id_union_local (σ σl : state) p :
    σl ⊆ σ → p ∉ used_proph_id σ →
    σ ∖ σl ⊆ state_upd_used_proph_id (union {[p]}) σ.
  Proof.
    destruct σl, σ.
    rewrite /subseteq /substate /difference /state_difference /=.
    intros [??] ?. split.
    - by apply map_subseteq_difference_l.
    - set_solver.
  Qed.

  Local Lemma atomic_base_step_ext_subset e σ σl κ κl v vl σ' σl' efs efsl :
    σl ⊆ σ →
    base_step e σl κl (Val vl) σl' efsl →
    base_step e σ κ (Val v) σ' efs →
    σ ∖ σl ⊆ σ'.
  Proof.
    intros Hsubset Hbase_stepl Hbase_step.
    revert κl Hbase_stepl.
    induction Hbase_step => κl Hbase_stepl;
    try solve [apply state_subseteq_difference_l; reflexivity].
    - (* AllocN *)
      trans σ; first by apply state_subseteq_difference_l.
      by apply state_init_heap_subseteq.
    - (* Free *)
      inversion Hbase_stepl. simplify_eq.
      apply subseteq_heap_update_local => //.
    - (* Store *)
      inversion Hbase_stepl. simplify_eq.
      apply subseteq_heap_update_local => //.
    - (* Xchg *)
      inversion Hbase_stepl. simplify_eq.
      apply subseteq_heap_update_local => //.
    - (* CmpXchg *)
      destruct b; last by apply state_subseteq_difference_l.
      inversion Hbase_stepl. simplify_eq.
      apply subseteq_heap_update_local => //.
    - (* FAA *)
      inversion Hbase_stepl. simplify_eq.
      apply subseteq_heap_update_local => //.
    - (* NewProph *)
      apply subseteq_used_proph_id_union_local => //.
    - (* Resolve *)
      inversion Hbase_stepl. simplify_eq.
      eauto.
  Qed.

  Local Lemma prim_step_ext_subset e σ κ e' σ' efs σl :
    σl ⊆ σ → reducible e σl → prim_step e σ κ e' σ' efs →
    σ ∖ σl ⊆ σ'.
  Proof.
    intros Hsubset Hred Hprim_step.
    destruct Hprim_step as [K e_ e2_ -> -> Hbase_step]. simpl in *.
    destruct Hbase_step; try solve [apply state_subseteq_difference_l; reflexivity].
    - (* AllocN *)
      trans σ; first by apply state_subseteq_difference_l.
      by apply state_init_heap_subseteq.
    - (* Free *)
      apply reducible_free_loc in Hred as [??].
      apply subseteq_heap_update_local => //.
    - (* Store *)
      apply reducible_store_loc in Hred as [??].
      apply subseteq_heap_update_local => //.
    - (* Xchg *)
      apply reducible_xchg_loc in Hred as [??].
      apply subseteq_heap_update_local => //.
    - (* CmpXchg *)
      destruct b; last by apply state_subseteq_difference_l.
      apply reducible_cmpxchg_loc in Hred as [??].
      apply subseteq_heap_update_local => //.
    - (* FAA *)
      apply reducible_faa_loc in Hred as [??].
      apply subseteq_heap_update_local => //.
    - (* NewProph *)
      apply subseteq_used_proph_id_union_local => //.
    - (* Resolve *)
      eapply reducible_resolve_red in Hred as [Hin (?&?&?&?&Hbase_step')]; last eassumption.
      by eapply atomic_base_step_ext_subset.
  Qed.

  Local Lemma fresh_heap_mono (h h' : gmap loc (option val) ) n (l : loc) :
    h ⊆ h' →
    (∀ i : Z, (0 ≤ i)%Z → (i < n)%Z → h' !! (l +ₗ i) = None) →
    (∀ i : Z, (0 ≤ i)%Z → (i < n)%Z → h !! (l +ₗ i) = None).
  Proof.
    intros Hsubset Hfresh i H0i Hin.
    eauto using lookup_weaken_None.
  Qed.

  Local Lemma init_heap_local (σ σl : state) l n v :
    σl ⊆ σ → (0 < n)%Z →
    (∀ i : Z, (0 ≤ i)%Z → (i < n)%Z → heap σ !! (l +ₗ i) = None) →
    state_init_heap l n v σ ∖ (σ ∖ σl) = state_init_heap l n v σl.
  Proof.
    intros Hsubstate H0n Hfresh.
    rewrite /state_init_heap /state_upd_heap /difference /state_difference /=.
    destruct Hsubstate.
    f_equal; last (rewrite difference_difference_r_L; set_solver).
    apply map_eq => l'.
    rewrite !lookup_difference !lookup_union.
    repeat case_match.
    - done.
    - apply eq_sym, union_None. split; last reflexivity.
      eapply map_disjoint_Some_r.
      + apply heap_array_map_disjoint.
        rewrite length_replicate Z2Nat.id; [done|lia].
      + eassumption.
    - f_equal. by eapply lookup_weaken.
    - f_equal. done.
  Qed.

  Local Lemma heap_update_local (σ σl : state) l v :
    σl ⊆ σ → is_Some (heap σl !! l) →
    state_upd_heap <[l:=v]> σ ∖ (σ ∖σl) = state_upd_heap <[l:=v]> σl.
  Proof.
    rewrite /state_upd_heap /subseteq /substate /difference /state_difference /=.
    intros [Hsubset ?] HisSome.
    f_equal; last (rewrite difference_difference_r_L; set_solver).
    apply map_eq => l'.
    destruct HisSome as [? Hσl_l].
    destruct (decide (l = l')) as [<-|Hne].
    - rewrite !lookup_difference !lookup_insert_eq Hσl_l //.
    - rewrite !lookup_difference !lookup_insert_ne //.
      destruct (heap σl !! l') eqn:?; first by eapply lookup_weaken.
      destruct (heap σ !! l'); done.
  Qed.

  Local Lemma used_proph_id_union_local (σ σl : state) p :
    σl ⊆ σ → p ∉ used_proph_id σ →
    state_upd_used_proph_id (union {[p]}) σ ∖ (σ ∖ σl) = state_upd_used_proph_id (union {[p]}) σl.
  Proof.
    rewrite /state_upd_used_proph_id /subseteq /substate /difference /state_difference /=.
    intros [? Hsubset] Hfresh.
    f_equal; first by apply heap_difference_difference_r.
    rewrite difference_union_distr_l_L.
    rewrite (difference_difference_r_L (used_proph_id σ)).
    set_solver.
  Qed.

  Local Lemma atomic_base_step_subset e σ σl κ κl v vl σ' σl' efs efsl  :
    σl ⊆ σ →
    base_step e σl κl (Val vl) σl' efsl →
    base_step e σ κ (Val v) σ' efs →
    base_step e σl κ (Val v) (σ'∖(σ∖σl)) efs.
  Proof.
    intros Hsubstate Hbase_stepl Hbase_step.
    remember (Val v) as val_v eqn:Heq.
    revert κl Hbase_stepl.
    induction Hbase_step => κl Hbase_stepl; try solve [
      inversion Hbase_stepl; simplify_eq;
      rewrite state_difference_difference_r //].
    - (* App (function call) *)
      inversion Hbase_stepl; simplify_eq.
      rename select (Val v = subst' _ _ _) into Heqv.
      rename select (Val vl = subst' _ _ _) into Heqvl.
      rewrite -Heqv in Heqvl.
      injection Heqvl as ->.
      rewrite state_difference_difference_r //.
    - (* AllocN *)
      inversion Hbase_stepl; simplify_eq.
      rewrite init_heap_local //.
      econstructor; first assumption.
      destruct Hsubstate.
      by eapply fresh_heap_mono.
    - (* Free *)
      inversion Hbase_stepl; simplify_eq.
      rewrite heap_update_local //.
    - (* Load *)
      inversion Hbase_stepl; simplify_eq.
      rename select (heap σ !! l = Some (Some v)) into Hlookup.
      assert (Hlookup': heap σ !! l = Some (Some vl)).
      { destruct Hsubstate. eapply lookup_weaken; eassumption. }
      rewrite Hlookup' in Hlookup.
      injection Hlookup as ->.
      rewrite state_difference_difference_r //.
    - (* Store *)
      inversion Hbase_stepl; simplify_eq.
      rewrite heap_update_local //.
    - (* Xchg *)
      inversion Hbase_stepl; simplify_eq.
      rename select (heap σ !! l = Some (Some v)) into Hlookup.
      assert (Hlookup': heap σ !! l = Some (Some vl)).
      { destruct Hsubstate. eapply lookup_weaken; eassumption. }
      rewrite Hlookup' in Hlookup.
      injection Hlookup as ->.
      rewrite heap_update_local //.
    - (* CmpXchg *)
      inversion Hbase_stepl; simplify_eq.
      rename select (heap σ !! l = Some (Some _)) into Hlookup.
      rename select (heap σl !! l = Some (Some _)) into Hlookupl.
      pose proof (lookup_weaken σl.(heap) σ.(heap) l _ Hlookupl (proj1 Hsubstate)) as Hlookup'.
      rewrite Hlookup' in Hlookup.
      injection Hlookup as ->.
      case_match.
      + rewrite heap_update_local //.
      + rewrite state_difference_difference_r //.
    - (* FAA *)
      inversion Hbase_stepl; simplify_eq.
      rename select (heap σ !! l = Some (Some _)) into Hlookup.
      rename select (heap σl !! l = Some (Some _)) into Hlookupl.
      pose proof (lookup_weaken σl.(heap) σ.(heap) l _ Hlookupl (proj1 Hsubstate)) as Hlookup'.
      rewrite Hlookup' in Hlookup.
      injection Hlookup as ->.
      rewrite heap_update_local //.
    - (* NewProph *)
      inversion Hbase_stepl; simplify_eq.
      rewrite used_proph_id_union_local //.
      constructor.
      destruct Hsubstate. set_solver.
    - (* Resolve *)
      inversion Hbase_stepl; simplify_eq.
      constructor; eauto.
  Qed.

  Lemma prim_step_subset e σ κ e' σ' efs σl :
    σl ⊆ σ → reducible e σl → prim_step e σ κ e' σ' efs →
    ∃ σ_ext σl', σl##σ_ext ∧ σl'##σ_ext ∧ σ = σl ∪ σ_ext ∧ σ' = σl' ∪ σ_ext ∧ prim_step e σl κ e' σl' efs.
  Proof.
    intros Hsubstate Hred Hprim_step.
    exists (σ∖σl), (σ'∖(σ∖σl)).
    assert (σl ## σ ∖ σl) as Hdisj1.
    {  apply (state_disjoint_difference_r1). reflexivity. }
    assert (σ' ∖ (σ ∖ σl) ## σ ∖ σl) as Hdisj2.
    { apply (state_disjoint_difference_l1). reflexivity. }
    split; last split; last split; last split; try assumption.
    { by apply state_union_difference. }
    { rewrite state_union_comm //.
      apply state_union_difference.
      by eapply prim_step_ext_subset. }

    destruct Hprim_step as [K e_ e2_ -> -> Hbase_step]. simpl in *.
    destruct Hbase_step; try solve [ econstructor; eauto;
      rewrite state_difference_difference_r //; econstructor; eauto].
    - (* AllocN *)
      econstructor; eauto.
      rewrite init_heap_local //.
      econstructor; eauto.
      destruct Hsubstate.
      by eapply fresh_heap_mono.
    - (* Free *)
      apply (reducible_free_loc) in Hred as [v' Hlookup].
      econstructor; eauto.
      rewrite heap_update_local //.
      econstructor; eauto.
    - (* Load *)
      apply (reducible_load_loc) in Hred as [v' Hlookup].
      pose proof (lookup_weaken σl.(heap) σ.(heap) l (Some v') Hlookup (proj1 Hsubstate)) as Hlookup'.
      simplify_eq.
      econstructor; eauto.
      rewrite state_difference_difference_r //.
      econstructor; eauto.
    - (* Store *)
      apply (reducible_store_loc) in Hred as [v' Hlookup].
      econstructor; eauto.
      rewrite heap_update_local //.
      econstructor; eauto.
    - (* Xchg *)
      apply (reducible_xchg_loc) in Hred as [v' Hlookup].
      pose proof (lookup_weaken σl.(heap) σ.(heap) l (Some v') Hlookup (proj1 Hsubstate)) as Hlookup'.
      simplify_eq.
      econstructor; eauto.
      rewrite heap_update_local //.
      econstructor; eauto.
    - (* CmpXchg *)
      apply (reducible_cmpxchg_loc) in Hred as [v' Hlookup].
      pose proof (lookup_weaken σl.(heap) σ.(heap) l (Some v') Hlookup (proj1 Hsubstate)) as Hlookup'.
      simplify_eq.
      econstructor; eauto.
      destruct (bool_decide (vl = v1)) eqn:Hbool_decide.
      + rewrite heap_update_local //.
        econstructor; eauto.
      + rewrite state_difference_difference_r //.
        econstructor; eauto.
    - (* FAA *)
      apply (reducible_faa_loc) in Hred as [i1' Hlookup].
      pose proof (lookup_weaken σl.(heap) σ.(heap) l (Some (LitV (LitInt i1'))) Hlookup (proj1 Hsubstate)) as Hlookup'.
      simplify_eq.
      econstructor; eauto.
      rewrite heap_update_local //.
      econstructor; eauto.
    - (* NewProph *)
      econstructor; eauto.
      rewrite used_proph_id_union_local //.
      econstructor; eauto.
      destruct Hsubstate.
      set_solver.
    - (* Resolve *)
      econstructor; eauto.
      eapply reducible_resolve_red in Hred as [Hin (κsl & vl & σl' & tsl & Hbase_step')];
        last eassumption.
      econstructor; eauto.
      by eapply atomic_base_step_subset.
  Qed.
End substate.

Section state.
  Context `{!heapGS_gen hlc Σ}.
  Implicit Types (e : expr) (σ : state) (κ κs : list observation) (efs : list expr).

  (* The ownership of a fragment of the program state. *)
  Definition own_state (σ : state) (ns : nat) (κs : list observation) (nt : nat) : iProp Σ :=
    ([∗ map] l↦ov ∈ σ.(heap), gen_heap.pointsto l (DfracOwn 1) ov) ∗
    ([∗ set] p ∈ σ.(used_proph_id), proph p (proph_list_resolves κs p)).

  Lemma own_state_empty ns κs nt : ⊢ own_state state_empty ns κs nt.
  Proof. rewrite /own_state big_sepM_empty big_sepS_empty. auto. Qed.

  Lemma own_state_agree σ ns κs nt σ' ns' κs' nt' :
    state_interp σ ns κs nt -∗ own_state σ' ns' κs' nt' -∗ ⌜σ' ⊆ σ⌝.
  Proof.
    iDestruct 1 as "(Hheap● & Hproph● & _)".
    iDestruct 1 as "[Hheap◯ Hproph◯]".
    iSplitL "Hheap● Hheap◯".
    - iAssert ([∗ map] l↦ov ∈ σ'.(heap), ⌜σ.(heap) !! l = Some ov⌝)%I with "[-]" as "%Hsubset";
        last by iPureIntro; apply map_subseteq_spec.
      rewrite !big_opM_map_to_list.
      remember (map_to_list σ'.(heap)) as L eqn:HeqL. clear HeqL σ'.
      iInduction L as [|l L].
      + rewrite !big_opL_nil. iFrame.
      + rewrite !big_opL_cons.
        iDestruct "Hheap◯" as "[Hpointsto Hheap◯]".
        iDestruct (gen_heap_valid with "Hheap● Hpointsto") as %Hlookup.
        iSplit; first done.
        iApply ("IHL" with "Hheap● Hheap◯").
    - iAssert ([∗ set] p ∈ σ'.(used_proph_id), ⌜p ∈ σ.(used_proph_id)⌝)%I with "[-]" as "%Hsubset";
        last by iPureIntro; set_solver.
      rewrite -(big_opM_gset_to_gmap (λ p (_ : ()), ⌜p ∈ used_proph_id σ⌝)%I _ ()).
      rewrite -(big_opM_gset_to_gmap (λ p (_ : ()), proph p (proph_list_resolves κs' p))%I _ ()).
      rewrite !big_opM_map_to_list.
      remember (map_to_list (gset_to_gmap () σ'.(used_proph_id))) as L eqn:HeqL. clear HeqL σ'.
      iInduction L as [|l L].
      + rewrite !big_opL_nil. iFrame.
      + rewrite !big_opL_cons.
        iDestruct "Hproph◯" as "[Hp Hproph◯]".
        iSplit.
        * iDestruct (proph_map_agree with "[$Hproph● $Hp]") as "[$ _]".
        * iApply ("IHL" with "Hproph● Hproph◯").
  Qed.

  Lemma own_state_canoicalize σ ns κs nt σ' ns' κs' nt' :
    state_interp σ ns κs nt -∗ own_state σ' ns' κs' nt' -∗
    state_interp σ ns κs nt ∗ own_state σ' ns κs nt.
  Proof.
    iIntros "H● H◯".
    iDestruct (own_state_agree with "H● H◯") as %[Hsubheap Hsubproph].
    iDestruct "H●" as "($ & Hproph● & $)".
    iDestruct "H◯" as "[$ Hproph◯]".
    rewrite -(big_opM_gset_to_gmap (λ p (_ : ()), proph p (proph_list_resolves κs p))%I _ ()).
    rewrite -(big_opM_gset_to_gmap (λ p (_ : ()), proph p (proph_list_resolves κs' p))%I _ ()).
    rewrite !big_opM_map_to_list.
    remember (map_to_list (gset_to_gmap () σ'.(used_proph_id))) as L eqn:HeqL. clear.
    iInduction L as [|l L].
    - rewrite !big_opL_nil. iFrame.
    - rewrite !big_opL_cons.
      iDestruct "Hproph◯" as "[Hp Hproph◯]".
      iDestruct (proph_map_agree with "[$Hproph● $Hp]") as %[_ ->].
      iFrame "Hp".
      iApply ("IHL" with "Hproph● Hproph◯").
  Qed.

  (* TODO: move to iris_heap_lang/primitive_laws.v *)
  Local Lemma state_interp_step σ ns κs nt :
    state_interp σ ns κs nt ==∗ state_interp σ (S ns) κs nt.
  Proof.
    iDestruct 1 as "($ & $ & Hstep)".
    by iApply primitive_laws.steps_auth_update_S.
  Qed.

  Local Lemma used_proph_id_grows e σ κ v σ' efs:
    base_step e σ κ (Val v) σ' efs →
    σ.(used_proph_id) ⊆ σ'.(used_proph_id).
  Proof.
    intros Hbase_step.
    induction Hbase_step; try done.
    - destruct b; simpl; reflexivity.
    - simpl. set_solver.
  Qed.

  Local Lemma atomic_base_step_state_update {e v' σ σ' σ_ext κ κs efs} :
    σ ## σ_ext → σ' ## σ_ext → base_step e σ κ (Val v') σ' efs →
    gen_heap_interp (σ.(heap) ∪ σ_ext.(heap)) -∗
    proph_map_interp (κ++κs) (σ.(used_proph_id) ∪ σ_ext.(used_proph_id)) -∗
    ([∗ map] l↦ov ∈ σ.(heap), gen_heap.pointsto l (DfracOwn 1) ov) -∗
    ([∗ set] p ∈ σ.(used_proph_id), proph p (proph_list_resolves (κ++κs) p)) ==∗
    gen_heap_interp (σ'.(heap) ∪ σ_ext.(heap)) ∗
    proph_map_interp κs (σ'.(used_proph_id) ∪ σ_ext.(used_proph_id)) ∗
    ([∗ map] l↦ov ∈ σ'.(heap), gen_heap.pointsto l (DfracOwn 1) ov) ∗
    ([∗ set] p ∈ σ'.(used_proph_id), proph p (proph_list_resolves κs p)).
  Proof.
    intros Hdisj1 Hdisj2 Hbase_step.
    revert κs.
    induction Hbase_step => κs';
      iIntros "Hheap● Hproph● Hheap◯ Hproph◯";
      rewrite ?length_nil ?left_id_L;
      iFrame; try done.
    - (* AllocN *)
      destruct σ as [h ?].
      destruct σ_ext as [h_ext ?].
      destruct Hdisj1 as [Hdisjh1 _].
      destruct Hdisj2 as [Hdisjh2 _].
      simpl in *.
      assert (heap_array l (replicate (Z.to_nat n) v) ##ₘ h).
      { apply heap_array_map_disjoint.
        rewrite length_replicate Z2Nat.id; auto with lia. }
      iMod (gen_heap_alloc_big _ (heap_array _ (replicate (Z.to_nat n) v)) with "Hheap●")
        as "(Hheap● & Hl & _)".
      { apply map_disjoint_union_r_2.
        - eassumption.
        - apply map_disjoint_union_l in Hdisjh2 as [??].
          assumption. }
      rewrite assoc_L big_sepM_union //.
      by iFrame.
    - (* Free *)
      destruct σ as [h p].
      destruct σ_ext as [h_ext ?].
      destruct Hdisj1 as [Hdisjh1 _].
      destruct Hdisj2 as [Hdisjh2 _].
      simpl in *.
      rewrite (big_sepM_delete _ h l) //.
      iDestruct "Hheap◯" as "[Hl Hheap◯]".
      iMod (gen_heap_update with "Hheap● Hl") as "[Heap● Hl]".
      rewrite insert_union_l big_sepM_insert_delete.
      by iFrame.
    - (* Store *)
      destruct σ as [h ?].
      destruct σ_ext as [h_ext ?].
      destruct Hdisj1 as [Hdisjh1 _].
      destruct Hdisj2 as [Hdisjh2 _].
      simpl in *.
      rewrite (big_sepM_delete _ h l) //.
      iDestruct "Hheap◯" as "[Hl Hheap◯]".
      iMod (gen_heap_update with "Hheap● Hl") as "[Heap● Hl]".
      rewrite insert_union_l big_sepM_insert_delete.
      by iFrame.
    - (* Xchg *)
      destruct σ as [h ?].
      destruct σ_ext as [h_ext ?].
      destruct Hdisj1 as [Hdisjh1 _].
      destruct Hdisj2 as [Hdisjh2 _].
      simpl in *.
      rewrite (big_sepM_delete _ h l) //.
      iDestruct "Hheap◯" as "[Hl Hheap◯]".
      iMod (gen_heap_update with "Hheap● Hl") as "[Heap● Hl]".
      rewrite insert_union_l big_sepM_insert_delete.
      by iFrame.
    - (* CmpXchg *)
      destruct b; iFrame; last done.
      destruct σ as [h ?].
      destruct σ_ext as [h_ext ?].
      destruct Hdisj1 as [Hdisjh1 _].
      destruct Hdisj2 as [Hdisjh2 _].
      simpl in *.
      rewrite (big_sepM_delete _ h l) //.
      iDestruct "Hheap◯" as "[Hl Hheap◯]".
      iMod (gen_heap_update with "Hheap● Hl") as "[Heap● Hl]".
      rewrite insert_union_l big_sepM_insert_delete.
      by iFrame.
    - (* FAA *)
      destruct σ as [h pm].
      destruct σ_ext as [h_ext pm_ext].
      destruct Hdisj1 as [Hdisjh1 Hdisjpm1].
      destruct Hdisj2 as [Hdisjh2 Hdisjpm2].
      simpl in *.
      rewrite (big_sepM_delete _ h l) //.
      iDestruct "Hheap◯" as "[Hl Hheap◯]".
      iMod (gen_heap_update with "Hheap● Hl") as "[Heap● Hl]".
      rewrite insert_union_l big_sepM_insert_delete.
      by iFrame.
    - (* NewProp *)
      destruct σ as [? pm].
      destruct σ_ext as [? pm_ext].
      destruct Hdisj1 as [_ Hdisjpm1].
      destruct Hdisj2 as [_ Hdisjpm2].
      simpl in *.
      iMod (proph_map_new_proph p with "Hproph●") as "[Hproph● Hp]";
        first set_solver.
      rewrite assoc_L big_sepS_union; last set_solver.
      rewrite big_sepS_singleton.
      by iFrame.
    - (* Resolve *)
      rewrite -assoc_L.
      iMod (IHHbase_step Hdisj1 Hdisj2 with "Hheap● Hproph● Hheap◯ Hproph◯")
        as "($ & Hproph● & $ & Hproph◯)".
      assert (Hin: p ∈ σ'.(used_proph_id)).
      { apply used_proph_id_grows in Hbase_step. set_solver. }
      rewrite !(big_sepS_delete _ (σ'.(used_proph_id)) p) //.
      iDestruct "Hproph◯" as "[Hp Hproph◯]".
      iMod (proph_map_resolve_proph with "[$Hproph● $Hp]") as (κs'' Heq) "[$ Hp]".
      rewrite /= decide_True // in Heq.
      injection Heq as <-.
      iFrame "Hp".
      iApply (big_sepS_mono with "Hproph◯").
      iIntros (p' Hin') "Hp".
      rewrite /= decide_False; [done|set_solver].
  Qed.

  Lemma state_update e e' σ σ' σ_ext ns ns' κ κs κ' nt nt' efs :
    σ ## σ_ext → σ' ## σ_ext → prim_step e σ κ e' σ' efs →
    state_interp (σ∪σ_ext) ns (κ++κs) nt -∗ own_state σ ns' κ' nt' ={∅}=∗
    state_interp (σ'∪σ_ext) (S ns) κs (length efs + nt) ∗ own_state σ' (S ns) κs (length efs + nt).
  Proof.
    iIntros (Hdisj1 Hdisj2 Hprim_step) "H● H◯".
    iDestruct (own_state_canoicalize with "H● H◯") as "[H● H◯]".
    iDestruct "H●" as "(Hheap● & Hproph● & Hstep)".
    iDestruct "H◯" as "[Hheap◯ Hproph◯]".
    iMod (primitive_laws.steps_auth_update_S with "Hstep") as "$".
    clear ns' κ' nt'.

    destruct Hprim_step as [K e_ e2_ -> -> Hbase_step]. simpl in *.
    destruct Hbase_step; rewrite ?length_nil ?left_id_L;
      iFrame; try done.
    - (* AllocN *)
      destruct σ as [h ?].
      destruct σ_ext as [h_ext ?].
      destruct Hdisj1 as [Hdisjh1 _].
      destruct Hdisj2 as [Hdisjh2 _].
      simpl in *.
      assert (heap_array l (replicate (Z.to_nat n) v) ##ₘ h).
      { apply heap_array_map_disjoint.
        rewrite length_replicate Z2Nat.id; auto with lia. }
      iMod (gen_heap_alloc_big _ (heap_array _ (replicate (Z.to_nat n) v)) with "Hheap●")
        as "(Hheap● & Hl & _)".
      { apply map_disjoint_union_r_2.
        - eassumption.
        - apply map_disjoint_union_l in Hdisjh2 as [??].
          assumption. }
      rewrite assoc_L big_sepM_union //.
      by iFrame.
    - (* Free *)
      destruct σ as [h p].
      destruct σ_ext as [h_ext ?].
      destruct Hdisj1 as [Hdisjh1 _].
      destruct Hdisj2 as [Hdisjh2 _].
      simpl in *.
      rewrite (big_sepM_delete _ h l) //.
      iDestruct "Hheap◯" as "[Hl Hheap◯]".
      iMod (gen_heap_update with "Hheap● Hl") as "[Heap● Hl]".
      rewrite insert_union_l big_sepM_insert_delete.
      by iFrame.
    - (* Store *)
      destruct σ as [h ?].
      destruct σ_ext as [h_ext ?].
      destruct Hdisj1 as [Hdisjh1 _].
      destruct Hdisj2 as [Hdisjh2 _].
      simpl in *.
      rewrite (big_sepM_delete _ h l) //.
      iDestruct "Hheap◯" as "[Hl Hheap◯]".
      iMod (gen_heap_update with "Hheap● Hl") as "[Heap● Hl]".
      rewrite insert_union_l big_sepM_insert_delete.
      by iFrame.
    - (* Xchg *)
      destruct σ as [h ?].
      destruct σ_ext as [h_ext ?].
      destruct Hdisj1 as [Hdisjh1 _].
      destruct Hdisj2 as [Hdisjh2 _].
      simpl in *.
      rewrite (big_sepM_delete _ h l) //.
      iDestruct "Hheap◯" as "[Hl Hheap◯]".
      iMod (gen_heap_update with "Hheap● Hl") as "[Heap● Hl]".
      rewrite insert_union_l big_sepM_insert_delete.
      by iFrame.
    - (* CmpXchg *)
      destruct b; iFrame; last done.
      destruct σ as [h ?].
      destruct σ_ext as [h_ext ?].
      destruct Hdisj1 as [Hdisjh1 _].
      destruct Hdisj2 as [Hdisjh2 _].
      simpl in *.
      rewrite (big_sepM_delete _ h l) //.
      iDestruct "Hheap◯" as "[Hl Hheap◯]".
      iMod (gen_heap_update with "Hheap● Hl") as "[Heap● Hl]".
      rewrite insert_union_l big_sepM_insert_delete.
      by iFrame.
    - (* FAA *)
      destruct σ as [h pm].
      destruct σ_ext as [h_ext pm_ext].
      destruct Hdisj1 as [Hdisjh1 Hdisjpm1].
      destruct Hdisj2 as [Hdisjh2 Hdisjpm2].
      simpl in *.
      rewrite (big_sepM_delete _ h l) //.
      iDestruct "Hheap◯" as "[Hl Hheap◯]".
      iMod (gen_heap_update with "Hheap● Hl") as "[Heap● Hl]".
      rewrite insert_union_l big_sepM_insert_delete.
      by iFrame.
    - (* NewProp *)
      destruct σ as [? pm].
      destruct σ_ext as [? pm_ext].
      destruct Hdisj1 as [_ Hdisjpm1].
      destruct Hdisj2 as [_ Hdisjpm2].
      simpl in *.
      iMod (proph_map_new_proph p with "Hproph●") as "[Hproph● Hp]";
        first set_solver.
      rewrite assoc_L big_sepS_union; last set_solver.
      rewrite big_sepS_singleton.
      by iFrame.
    - (* Resolve *)
      rewrite -assoc_L.
      iMod (atomic_base_step_state_update Hdisj1 Hdisj2 Hbase_step with "Hheap● Hproph● Hheap◯ Hproph◯")
        as "($ & Hproph● & $ & Hproph◯)".
      assert (Hin: p ∈ σ'.(used_proph_id)).
      { apply used_proph_id_grows in Hbase_step. set_solver. }
      rewrite !(big_sepS_delete _ (σ'.(used_proph_id)) p) //.
      iDestruct "Hproph◯" as "[Hp Hproph◯]".
      iMod (proph_map_resolve_proph with "[$Hproph● $Hp]") as (κs' Heq) "[$ Hp]".
      rewrite /= decide_True // in Heq.
      injection Heq as <-.
      iFrame "Hp".
      iApply (big_sepS_mono with "Hproph◯").
      iIntros (p' Hin') "Hp".
      rewrite /= decide_False; [done|set_solver].
  Qed.

  (*Lemma own_state_reducible e σ ns κs nt σ' ns' κs' nt' :
    reducible e σ' →
    state_interp σ ns κs nt -∗ own_state σ' ns' κs' nt' -∗ ⌜reducible e σ⌝.
  Proof.
    iIntros (Hred) "H● H◯".
    iDestruct (own_state_agree with "H● H◯") as %Hsubstate.
    iPureIntro. by eapply reducible_mono.
  Qed.*)

  Lemma own_state_update e σ ns κ κs nt σl ns' κ' nt' :
    reducible e σl →
    state_interp σ ns (κ++κs) nt -∗ own_state σl ns' κ' nt' -∗
    ⌜reducible e σ⌝ ∗
    (∀ e' σ' efs, ⌜prim_step e σ κ e' σ' efs⌝ ={∅}=∗
    ∃ σl', ⌜prim_step e σl κ e' σl' efs⌝ ∗ state_interp σ' (S ns) κs (length efs + nt) ∗ own_state σl' (S ns) κs (length efs + nt)).
  Proof.
    iIntros (Hred) "H● H◯".
    iDestruct (own_state_agree with "H● H◯") as %Hsubstate.
    iSplit. { iPureIntro. by eapply reducible_mono. }
    iIntros (e' σ' efs Hprim_step).
    iDestruct (own_state_agree with "H● H◯") as %Hσlσ.
    edestruct (prim_step_subset) as (σ_ext & σl2 & Hσl1_dis & Hσl2_dis & Heq1 & Heq2 & Hprim_step_l).
    { exact Hσlσ. } { exact Hred. } { exact Hprim_step. }
    subst σ σ'.
    by iMod (state_update with "H● H◯") as "[$ $]".
  Qed.
End state.
End colang.

Global Program Instance heaplang_complete `{!heapGS_gen hlc Σ} : coirisG_gen hlc heap_lang Σ := {
  state_empty := colang.state_empty;
  own_state := colang.own_state;
  own_state_empty := colang.own_state_empty;
  own_state_update := colang.own_state_update;
}.
Solve Obligations with auto.
