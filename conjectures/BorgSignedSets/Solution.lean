import conjectures.BorgSignedSets.Exceptional
import conjectures.BorgSignedSets.Extremal
import conjectures.BorgSignedSets.Selector
import conjectures.BorgSignedSets.Stars

namespace BorgSignedSets

/-- The signed-set conjecture for every finite family and every alphabet of size at least two. -/
theorem signed_sets : Conjecture := by
  intro n k _ hk F hF hn
  obtain ⟨B, hB⟩ := (show F.Nonempty from hF)
  obtain ⟨i, _⟩ := hn B hB
  obtain ⟨j, _, hmax⟩ := Finset.exists_max_image Finset.univ (degree F k) ⟨i, Finset.mem_univ _⟩
  have largest (t : Fin n) : degree F k t ≤ degree F k j := hmax t (Finset.mem_univ t)
  constructor
  · refine ⟨star j 0, star_intersecting F j 0, ⟨j, 0, fun B _ b => mem_star j 0 B b⟩, ?_⟩
    intro A hA
    rw [size_star]
    obtain ⟨h, cert⟩ := exists_selector F A hk hF hn hA
    exact size_le_largest_star F A h cert hk j largest
  · constructor
    · rintro ⟨A, hA, hstar, hext⟩
      obtain ⟨h, cert⟩ := exists_selector F A hk hF hn hA
      exact (star_or_exception F A hk hF hn hA h cert j largest (hext j)).resolve_left hstar
    · exact exceptional_witness hF hn

end BorgSignedSets
