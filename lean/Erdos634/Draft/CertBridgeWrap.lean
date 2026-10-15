import Erdos634.CertBridge

namespace Erdos634.Draft.CertBridgeWrap

open Erdos634.CertBridge
open Erdos634.Geometry MeasureTheory

-- Re-exports: certified-search bridge (CongruentDissection from a certificate)

theorem wrap_ofCert_target {N : ℕ} (target model : Tri) (tile : Fin N → Tri)
    (hd01 : ∀ i, dist ((tile i).pts 0) ((tile i).pts 1) = dist (model.pts 0) (model.pts 1))
    (hd12 : ∀ i, dist ((tile i).pts 1) ((tile i).pts 2) = dist (model.pts 1) (model.pts 2))
    (hd20 : ∀ i, dist ((tile i).pts 2) ((tile i).pts 0) = dist (model.pts 2) (model.pts 0))
    (hsub : ∀ i, (tile i).carrier ⊆ target.carrier)
    (hdisj : Pairwise fun i j =>
      Disjoint (interior (tile i).carrier) (interior (tile j).carrier))
    (hdet : ∑ i, |Erdos634.AreaDet.detTri (tile i)| = |Erdos634.AreaDet.detTri target|) :
    (ofCert target model tile hd01 hd12 hd20 hsub hdisj hdet).target = target :=
  ofCert_target target model tile hd01 hd12 hd20 hsub hdisj hdet

theorem wrap_ofCert_model {N : ℕ} (target model : Tri) (tile : Fin N → Tri)
    (hd01 : ∀ i, dist ((tile i).pts 0) ((tile i).pts 1) = dist (model.pts 0) (model.pts 1))
    (hd12 : ∀ i, dist ((tile i).pts 1) ((tile i).pts 2) = dist (model.pts 1) (model.pts 2))
    (hd20 : ∀ i, dist ((tile i).pts 2) ((tile i).pts 0) = dist (model.pts 2) (model.pts 0))
    (hsub : ∀ i, (tile i).carrier ⊆ target.carrier)
    (hdisj : Pairwise fun i j =>
      Disjoint (interior (tile i).carrier) (interior (tile j).carrier))
    (hdet : ∑ i, |Erdos634.AreaDet.detTri (tile i)| = |Erdos634.AreaDet.detTri target|) :
    (ofCert target model tile hd01 hd12 hd20 hsub hdisj hdet).model = model :=
  ofCert_model target model tile hd01 hd12 hd20 hsub hdisj hdet

theorem wrap_ofCert_volume {N : ℕ} (target model : Tri) (tile : Fin N → Tri)
    (hd01 : ∀ i, dist ((tile i).pts 0) ((tile i).pts 1) = dist (model.pts 0) (model.pts 1))
    (hd12 : ∀ i, dist ((tile i).pts 1) ((tile i).pts 2) = dist (model.pts 1) (model.pts 2))
    (hd20 : ∀ i, dist ((tile i).pts 2) ((tile i).pts 0) = dist (model.pts 2) (model.pts 0))
    (hsub : ∀ i, (tile i).carrier ⊆ target.carrier)
    (hdisj : Pairwise fun i j =>
      Disjoint (interior (tile i).carrier) (interior (tile j).carrier))
    (hdet : ∑ i, |Erdos634.AreaDet.detTri (tile i)| = |Erdos634.AreaDet.detTri target|) :
    volume target.carrier = (N : ENNReal) * volume model.carrier :=
  ofCert_volume target model tile hd01 hd12 hd20 hsub hdisj hdet

example : True := trivial

#print axioms Erdos634.CertBridge.ofCert_volume

end Erdos634.Draft.CertBridgeWrap
