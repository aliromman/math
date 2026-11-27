module

public import conjectures.Hypertriangulations.Mesh
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section
noncomputable section
namespace Hypertriangulations
namespace Boundary
open Set Finset Filter
open scoped Topology
variable {V : Type*} [Fintype V] [DecidableEq V] {P : V→Plane} {E : V→V→Prop}

def mid (a b : Plane) := (1/2:ℝ) • a + (1/2:ℝ) • b
def toward (a b : Plane) (t : ℝ) := (1-t) • a + t • b

omit [Fintype V] in
theorem edge_info {f : Face V} {i j : V} (h : f.edge i j) (hp : 0<f.area P) :
    ∃ k, f.vertices={i,j,k} ∧ 0<orient (P i) (P j) (P k) := by
  unfold Face.area at hp
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact ⟨f.c,rfl,hp⟩
  · exact ⟨f.a,by ext; simp [Face.vertices]; tauto, by rwa [orient_cycle]⟩
  · exact ⟨f.b,by ext; simp [Face.vertices]; tauto,
      by simpa only [orient_cycle (P f.b) (P f.c) (P f.a),orient_cycle (P f.a) (P f.b) (P f.c)] using hp⟩

omit [Fintype V] in
theorem edge_cases {f : Face V} {i j : V} (ne : i≠j) (hi : i∈f.vertices) (hj : j∈f.vertices) :
    f.edge i j ∨ f.edge j i := by
  simp only [Face.vertices,Finset.mem_insert,Finset.mem_singleton] at hi hj
  unfold Face.edge
  grind

omit [DecidableEq V] in
theorem orient_eval (a b : Plane) {w : V→ℝ} (hw : probability w) :
    orient a b (eval P w) = ∑ i, w i * orient a b (P i) := by
  have coeff (p : Plane) : orient a b p =
      (b.1-a.1)*p.2 - (b.2-a.2)*p.1 + ((b.2-a.2)*a.1-(b.1-a.1)*a.2) := by
    unfold orient; ring
  let K := (b.2-a.2)*a.1-(b.1-a.1)*a.2
  change _=∑ i, w i * orient a b (P i)
  simp_rw [coeff]
  simp only [eval,Prod.fst_sum,Prod.snd_sum,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  change (b.1-a.1)*(∑ i,w i*(P i).2) - (b.2-a.2)*(∑ i,w i*(P i).1) + K =
    ∑ i,w i*((b.1-a.1)*(P i).2-(b.2-a.2)*(P i).1+K)
  simp only [mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  rw [←Finset.sum_mul,hw.2,one_mul]
  simp only [Finset.mul_sum]
  congr 2 <;> apply Finset.sum_congr rfl <;> intros <;> ring

theorem edge_nonneg {f : Face V} (hp : 0<f.area P) {i j : V} (e : f.edge i j)
    {y : Plane} (hy : y∈f.realize P) : 0≤orient (P i) (P j) y := by
  obtain ⟨k,hv,hk⟩ := edge_info e hp
  obtain ⟨w,hw,hs,rfl⟩ := hy
  rw [orient_eval _ _ hw]
  refine sum_nonneg fun z _ => ?_
  by_cases hz : z∈f.vertices
  · rw [hv] at hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl|rfl|rfl
    · simp [orient]
    · simp [orient,mul_comm]
    · exact mul_nonneg (hw.1 _) hk.le
  · simp [hs z hz]

theorem realize_closed (P : V→Plane) (f : Face V) : IsClosed (f.realize P) := by
  classical
  let W : Set (V→ℝ) := {w | probability w ∧ supported w f.vertices}
  have closed : IsClosed W := by
    have h1 : IsClosed {w : V→ℝ | ∀ i, 0≤w i} := by
      simp_rw [Set.ofPred_forall]
      exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    have h2 : IsClosed {w : V→ℝ | ∑ i,w i=1} :=
      isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
    have h3 : IsClosed {w : V→ℝ | ∀ i, i∉f.vertices → w i=0} := by
      simp_rw [Set.ofPred_forall]
      exact isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_eq (continuous_apply i) continuous_const
    exact (h1.inter h2).inter h3
  have sub : W⊆Icc (0:V→ℝ) 1 := by
    intro w hw
    refine ⟨hw.1.1,fun i => ?_⟩
    exact (single_le_sum (f:=w) (fun j _ => hw.1.1 j) (mem_univ i)).trans_eq hw.1.2
  have eq : f.realize P=eval P '' W := by
    ext y
    change (∃ w, probability w ∧ supported w f.vertices ∧ eval P w=y) ↔ ∃ w, (probability w ∧ supported w f.vertices) ∧ eval P w=y
    tauto
  rw [eq]
  exact ((isCompact_Icc.of_isClosed_subset closed sub).image
    (continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const)).isClosed

def middle (i j : V) : V→ℝ := massAt i (1/2)+massAt j (1/2)

theorem middle_probability (i j : V) : probability (middle i j) := by
  refine ⟨fun z => ?_, by simp [middle, Finset.sum_add_distrib]; norm_num⟩
  simp only [middle,Pi.add_apply,massAt]; positivity

theorem middle_eval (i j : V) : eval P (middle i j)=mid (P i) (P j) := by
  simp [middle,mid,eval_add]

omit [Fintype V] in
theorem middle_mem {f : Face V} {i j : V} (hi : i∈f.vertices) (hj : j∈f.vertices) :
    supported (middle i j) f.vertices := by
  intro z hz
  have a : z≠i := fun e => hz (e ▸ hi)
  have b : z≠j := fun e => hz (e ▸ hj)
  simp [middle,massAt,a,b]

theorem incident_nearby (T : Mesh P E) {f : Face V} (hf : f∈T.faces)
    {i j : V} (hi : i∈f.vertices) (hj : j∈f.vertices) :
    ∀ᶠ y in 𝓝 (mid (P i) (P j)), ∀ t∈T.faces, y∈t.realize P → i∈t.vertices ∧ j∈t.vertices := by
  classical
  have wm : middle i j ∈ weights T.faces := ⟨middle_probability _ _,f,hf,middle_mem hi hj⟩
  refine (eventually_all_finset T.faces).mpr fun t ht => ?_
  by_cases H : i∈t.vertices ∧ j∈t.vertices
  · exact Eventually.of_forall fun _ _ => H
  have h : mid (P i) (P j)∉t.realize P := by
    rintro ⟨w,hw,hs,he⟩
    have eq := T.embedded ⟨hw,t,ht,hs⟩ wm (he.trans (middle_eval i j).symm)
    subst w
    have nonzero (a b : V) : 0<middle a b a := by simp [middle,massAt]; split <;> norm_num
    apply H
    constructor
    · by_contra absent; exact (nonzero i j).ne' (hs i absent)
    · by_contra absent
      have zz := hs j absent
      have pos : 0<middle i j j := by simp [middle,massAt]; split <;> norm_num
      exact pos.ne' zz
  filter_upwards [(realize_closed P t).isOpen_compl.mem_nhds h] with y hy
  exact fun h' => (hy h').elim

theorem side_toward (a b z : Plane) (t : ℝ) :
    orient a b (toward (mid a b) z t) = t*orient a b z := by
  simp [orient,toward,mid]; ring

private theorem inside_near (a b c z : Plane) (hc : 0<orient a b c) (hz : 0<orient a b z) :
    ∀ᶠ t in 𝓝[>] (0:ℝ), StrictInside a b c (toward (mid a b) z t) := by
  have near (p q : Plane) (h : 0<orient (mid a b) p q) :
      ∀ᶠ t in 𝓝[>] (0:ℝ), 0<orient (toward (mid a b) z t) p q := by
    have cont : Continuous (fun t => orient (toward (mid a b) z t) p q) := by
      unfold orient toward; fun_prop
    have h0 : 0<orient (toward (mid a b) z 0) p q := by simpa [toward] using h
    exact (cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually
      (isOpen_Ioi.mem_nhds h0)
  have h1 : orient (mid a b) b c=orient a b c/2 := by simp [orient,mid]; ring
  have h2 : orient (mid a b) c a=orient a b c/2 := by simp [orient,mid]; ring
  filter_upwards [self_mem_nhdsWithin (s:=Ioi (0:ℝ)) (a:=0),
    near b c (by rw [h1]; linarith),near c a (by rw [h2]; linarith)] with t ht H1 H2
  apply Or.inl
  refine ⟨?_,H1,H2⟩
  rw [←orient_cycle (toward (mid a b) z t) a b,side_toward]
  exact mul_pos ht hz

theorem same_left (T : Mesh P E) {f u : Face V} (hf : f∈T.faces) (hu : u∈T.faces)
    {i j : V} (ef : f.edge i j) (eu : u.edge i j) : f=u := by
  obtain ⟨k,fv,fpos⟩ := edge_info ef (T.positive _ hf)
  obtain ⟨m,uv,upos⟩ := edge_info eu (T.positive _ hu)
  have A := inside_near (P i) (P j) (P k) (P k) fpos fpos
  have B := inside_near (P i) (P j) (P m) (P k) upos fpos
  obtain ⟨t,t1,t2⟩ := (A.and B).exists
  obtain ⟨w,hw,sw,ew,pw⟩ := inside_coordinates (f:=⟨i,j,k⟩) fpos t1
  obtain ⟨v,hv,sv,ev,pv⟩ := inside_coordinates (f:=⟨i,j,m⟩) upos t2
  change supported w {i,j,k} at sw
  change supported v {i,j,m} at sv
  change ∀ z∈({i,j,k}:Finset V),0<w z at pw
  change ∀ z∈({i,j,m}:Finset V),0<v z at pv
  rw [←fv] at sw pw
  rw [←uv] at sv pv
  have same := T.embedded ⟨hw,f,hf,sw⟩ ⟨hv,u,hu,sv⟩ (ew.trans ev.symm)
  subst v
  apply T.unique_faces _ hf _ hu
  ext z
  constructor
  · intro hz
    by_contra h
    exact (pw _ hz).ne' (sv z h)
  · intro hz
    by_contra h
    exact (pv _ hz).ne' (sw z h)

omit [Fintype V] [DecidableEq V] in
theorem mid_hull (P : V→Plane) (i j : V) : mid (P i) (P j) ∈ convexHull ℝ (range P) :=
  convex_convexHull ℝ (range P) (subset_convexHull ℝ (range P) ⟨i,rfl⟩) (subset_convexHull ℝ (range P) ⟨j,rfl⟩)
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (0:ℝ)≤1/2) (by norm_num)

theorem opposite (T : Mesh P E) {f : Face V} (hf : f∈T.faces) {i j z : V}
    (fe : f.edge i j) (hz : orient (P i) (P j) (P z)<0) : ∃ s∈T.faces,s.edge j i := by
  obtain ⟨k,hv,hk⟩ := edge_info fe (T.positive _ hf)
  have hi : i∈f.vertices := by simp [hv]
  have hj : j∈f.vertices := by simp [hv]
  have cont : Continuous (toward (mid (P i) (P j)) (P z)) := by unfold toward; fun_prop
  have near := (cont.continuousAt (x:=0)).tendsto.mono_left (nhdsWithin_le_nhds (s:=Ioi (0:ℝ)))
  have h0 : toward (mid (P i) (P j)) (P z) 0=mid (P i) (P j) := by simp [toward]
  rw [h0] at near
  have H := near.eventually (incident_nearby T hf hi hj)
  obtain ⟨t,hinc,ht⟩ := (H.and (Ioo_mem_nhdsGT (show (0:ℝ)<1 by norm_num))).exists
  have hull : toward (mid (P i) (P j)) (P z) t ∈ convexHull ℝ (range P) :=
    convex_convexHull ℝ _ (mid_hull P i j) (subset_convexHull ℝ _ ⟨z,rfl⟩)
      (sub_nonneg.mpr ht.2.le) ht.1.le (by ring)
  obtain ⟨w,⟨hw,s,hs,hsw⟩,ew⟩ := T.cover ⟨i,j,k,hk.ne'⟩ hull
  have hs' : toward (mid (P i) (P j)) (P z) t∈s.realize P := ⟨w,hw,hsw,ew⟩
  obtain ⟨l,r⟩ := hinc s hs hs'
  have ne : i≠j := by rintro rfl; simp at hk
  refine ⟨s,hs,(edge_cases ne l r).resolve_left fun e => ?_⟩
  have nonneg := edge_nonneg (T.positive _ hs) e hs'
  rw [side_toward] at nonneg
  exact (mul_neg_of_pos_of_neg ht.1 hz).not_ge nonneg


private theorem single_location {w : V→ℝ} (hw : probability w) {j : V}
    (h : ∀ z, z≠j → w z=0) : eval P w=P j := by
  have single : ∑ z,w z=w j := Finset.sum_eq_single j (fun z _ ne => h z ne) (by simp)
  have val : w j=1 := single.symm.trans hw.2
  have eq : w=massAt j 1 := by
    ext z
    by_cases he : z=j
    · subst z; simp [massAt,val]
    · simp [massAt,h z he,he]
  simp [eq]

theorem mid_ne_right {a b : Plane} (h : a≠b) : mid a b≠b := by
  intro e
  apply h
  ext
  · have h1 := congrArg Prod.fst e
    simp [mid] at h1
    linarith
  · have h2 := congrArg Prod.snd e
    simp [mid] at h2
    linarith

theorem mid_ne_left {a b : Plane} (h : a≠b) : mid a b≠a := by
  rw [show mid a b=mid b a by simp [mid,add_comm]]
  exact mid_ne_right h.symm

theorem exposed (T : Mesh P E) (noncol : ∃ a b c, orient (P a) (P b) (P c)≠0)
    {i j : V} (ne : P i≠ P j) (left : ∀ z,0≤orient (P i) (P j) (P z))
    (only : ∀ z,orient (P i) (P j) (P z)=0 → z=i ∨ z=j) :
    ∃ t∈T.faces, t.edge i j := by
  have he : orient (P i) (P j) (mid (P i) (P j))=0 := by simp [orient,mid]; ring
  obtain ⟨w,⟨hw,t,ht,hs⟩,ew⟩ := T.cover noncol (mid_hull P i j)
  have zero : ∑ k,w k*orient (P i) (P j) (P k)=0 := by rw [←orient_eval _ _ hw,ew,he]
  have sparse (k : V) (hi : k≠i) (hj : k≠j) : w k=0 := by
    have z := (sum_eq_zero_iff_of_nonneg (fun r (_ : r∈Finset.univ) => mul_nonneg (hw.1 r) (left r))).mp zero k (mem_univ k)
    exact (mul_eq_zero.mp z).resolve_right fun e => (only k e).elim hi hj
  have I : i∈t.vertices := by
    by_contra missing
    have e : eval P w=P j := single_location hw fun z hz => by
      by_cases v : z=i
      · exact v ▸ hs _ missing
      · exact sparse z v hz
    exact mid_ne_right ne (ew.symm.trans e)
  have J : j∈t.vertices := by
    by_contra missing
    have e : eval P w=P i := single_location hw fun z hz => by
      by_cases v : z=j
      · exact v ▸ hs _ missing
      · exact sparse z hz v
    exact mid_ne_left ne (ew.symm.trans e)
  have nlab : i≠j := fun e => ne (congrArg P e)
  refine ⟨t,ht,(edge_cases nlab I J).resolve_right fun e => ?_⟩
  obtain ⟨k,_,neg⟩ := edge_info e (T.positive _ ht)
  rw [orient_swap] at neg
  exact (left k).not_gt (neg_pos.mp neg)


end Boundary
end Hypertriangulations
end
