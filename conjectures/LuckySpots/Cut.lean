module

public import conjectures.LuckySpots.Parking

@[expose] public section
namespace LuckySpots
open List

private theorem park_comm (p q : ℕ) {L : List ℕ} (hs : L.Pairwise (·<·)) :
    park p (park q L)=park q (park p L) := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨hfirst,hrest⟩ := List.pairwise_cons.mp hs
    by_cases hp : p≤x <;> by_cases hq : q≤x
    · simp only [park,hp,hq,ite_true]
      cases xs with
      | nil => rfl
      | cons y ys =>
        have hxy := hfirst y (by simp)
        simp [park,le_trans hp hxy.le,le_trans hq hxy.le]
    · simp [park,hp,hq]
    · simp [park,hp,hq]
    · simp [park,hp,hq,ih hrest]

theorem vacant_perm {u v : List ℕ} (h : u.Perm v) {L : List ℕ} (hL : L.Pairwise (·<·)) :
    vacant L u=vacant L v := by
  induction h generalizing L with
  | nil => rfl
  | cons x h ih => exact ih (hL.sublist (park_sublist _ _))
  | swap x y xs => simp only [vacant_cons,park_comm x y hL]
  | trans h₁ h₂ ih₁ ih₂ => exact (ih₁ hL).trans (ih₂ hL)

theorem high_low_perm (j : ℕ) (w : List ℕ) : (upper j w++low j w).Perm w := by
  have en : (fun x : ℕ ↦ !decide (j≤x)) = fun x ↦ decide (x<j) := by
    funext x
    by_cases h : j≤x <;> simp [h,show x<j ↔ ¬j≤x by omega]
  simpa only [upper,low,en] using List.filter_append_perm (fun z : ℕ ↦ decide (j≤z)) w

theorem high_low_length (j : ℕ) (w : List ℕ) :
    (upper j w).length+(low j w).length=w.length := by
  simpa using (high_low_perm j w).length_eq

theorem accepted_shift (d : ℕ) (L w : List ℕ) :
    accepted (L.map (d+·)) (w.map (d+·)) ↔ accepted L w := by
  simp only [accepted_iff_length,vacant_shift,List.length_map]

private theorem above_only (j : ℕ) (L R w : List ℕ) (hL : ∀ x∈L, x<j) (hw : ∀ x∈w,j≤x) :
    vacant (L++R) w=L++vacant R w := by
  induction w generalizing R with
  | nil => rfl
  | cons p ps ih =>
    have hp := hw p (by simp)
    have miss : ¬fits p L := by
      rintro ⟨x,hx,he⟩
      have := hL _ hx
      omega
    simp only [vacant_cons,park_append_miss miss]
    exact ih _ (fun x hx ↦ hw x (by simp [hx]))

private theorem below_only (j : ℕ) (L R w : List ℕ) (hR : ∀ x∈R, j≤x) (hw : ∀ x∈w, x<j) :
    vacant (L++R) w=vacant L w++R.drop (w.length+(vacant L w).length-L.length) := by
  induction w generalizing L R with
  | nil => simp
  | cons p ps ih =>
    have hp := hw p (by simp)
    have ht : ∀ x∈ps,x<j := fun x hx ↦ hw x (by simp [hx])
    by_cases hit : fits p L
    · simp only [vacant_cons, park_append_hit hit, List.length_cons]
      rw [ih (park p L) R hR ht]
      have hlen := park_length hit
      congr 2
      omega
    · simp only [vacant_cons,park_append_miss hit,park_misses hit,List.length_cons]
      cases R with
      | nil => simp [park]
      | cons x xs =>
        have he : p≤x := le_trans hp.le (hR _ (by simp))
        simp only [park,he,ite_true]
        rw [ih L xs (fun y hy ↦ hR y (by simp [hy])) ht]
        have cap := vacant_capacity L ps
        rw [show ps.length+1+(vacant L ps).length-L.length=
          (ps.length+(vacant L ps).length-L.length)+1 by omega,List.drop_succ_cons]

/-- For a full lot, success splits at any cut into filling the lower sites and
parking every upper preference in the upper sites. -/
theorem full_cut (j b : ℕ) (w : List ℕ) (hw : w.length=j+b) :
    vacant (List.range (j+b)) w=[] ↔
      vacant (List.range j) (low j w)=[] ∧ accepted (List.range b) (high j w) := by
  let L := List.range j
  let R := (List.range b).map (j+·)
  let u := low j w
  let v := upper j w
  have hL : ∀ x∈L,x<j := fun _ h ↦ List.mem_range.mp h
  have hR : ∀ x∈R,j≤x := by
    intro x hx
    obtain ⟨y,_,rfl⟩ := List.mem_map.mp hx
    omega
  have hu : ∀ x∈u,x<j := by simp [u,low]
  have hv : ∀ x∈v,j≤x := by simp [v,upper]
  have eq := (vacant_perm (high_low_perm j w) (L:=List.range (j+b)) List.pairwise_lt_range).symm
  rw [eq,List.range_add]
  change vacant (L++R) (v++u)=[] ↔ vacant L u=[] ∧ _
  have app : vacant (L++R) (v++u) = vacant (vacant (L++R) v) u := by simp [vacant]
  rw [app,above_only j L R v hL hv,below_only j L (vacant R v) u (fun x hx ↦ hR x ((vacant_sublist _ _).subset hx)) hu]
  have ha : accepted R v ↔ accepted (List.range b) (high j w) := by
    dsimp [R,v]
    rw [upper_eq,accepted_shift]
  rw [←ha,accepted_iff_length]
  by_cases e : vacant L u=[]
  · have hl : L.length=j := by simp [L]
    have hr : R.length=b := by simp [R]
    have huv : v.length+u.length=j+b := (high_low_length j w).trans hw
    have vcap := vacant_capacity R v
    have ucap := vacant_capacity L u
    simp only [e,List.length_nil,Nat.add_zero] at ucap ⊢
    simp only [List.nil_append,true_and,List.drop_eq_nil_iff]
    omega
  · simp [e]

/-- Higher preferences cannot affect the luck of a lower site. -/
theorem lower_luck (j s : ℕ) (hs : s<j) (L R w : List ℕ)
    (hL : ∀ x∈L, x<j) (hR : ∀ x∈R, j≤x) :
    lucky s (L++R) w=lucky s L (low j w) := by
  induction w generalizing L R with
  | nil => rfl
  | cons p ps ih =>
    by_cases hp : p<j
    · have eqb : (L++R).contains s=L.contains s := by
        have h : s∉R := fun h ↦ hs.not_ge (hR _ h)
        simp [h]
      have lo : low j (p::ps)=p::low j ps := by simp [low,hp]
      simp only [lucky,lo,eqb]
      by_cases hit : fits p L
      · rw [park_append_hit hit,ih (park p L) R (fun x hx ↦ hL x ((park_sublist _ _).subset hx)) hR]
      · rw [park_append_miss hit,park_misses hit,ih L (park p R) hL (fun x hx ↦ hR x ((park_sublist _ _).subset hx))]
    · have hn : p≠s := by omega
      have hm : ¬fits p L := by
        rintro ⟨x,hx,he⟩
        have := hL x hx
        omega
      have lo : low j (p::ps)=low j ps := by simp [low,hp]
      simpa [lucky,hn,lo,park_append_miss hm] using
        ih L (park p R) hL (fun x hx ↦ hR x ((park_sublist _ _).subset hx))

end LuckySpots
