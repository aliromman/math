module

public import conjectures.PeakRootBounds.Disk
public import conjectures.PeakRootBounds.HalfPlane
public import conjectures.PeakRootBounds.Statement

@[expose] public section
namespace PeakRootBounds

/-- Both bounds in Billey, Fahrbach and Talmage's complex-root conjecture. -/
theorem complex_root_bounds : Conjecture := by
  intro S hS hne z hz
  exact ⟨le_of_not_gt (fun h => peak_disk S hS hne h hz),
    le_of_not_gt (fun h => peak_half_plane S hS hne h hz)⟩

end PeakRootBounds
