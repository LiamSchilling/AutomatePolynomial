import AutomatePolynomial.Util.MvPolynomial
import AutomatePolynomial.Util.Hyperlist

namespace MvPolynomial

variable [CommSemiring R]

-- compute polynomial coefficients
class MvCoeff (p : MvPolynomial σ R) where
  I : List σ
  C : Hyperlist R I.length

end MvPolynomial
