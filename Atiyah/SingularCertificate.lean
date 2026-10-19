import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-! Exact arithmetic certificates in ℤ[√2, √962]. -/
namespace Atiyah.SingularCertificate

structure Quad where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  deriving DecidableEq, Repr

def Quad.add (p q : Quad) : Quad := ⟨p.a+q.a,p.b+q.b,p.c+q.c,p.d+q.d⟩
def Quad.neg (p : Quad) : Quad := ⟨-p.a,-p.b,-p.c,-p.d⟩
def Quad.mul (p q : Quad) : Quad :=
  ⟨p.a*q.a+2*p.b*q.b+962*p.c*q.c+1924*p.d*q.d,
   p.a*q.b+p.b*q.a+962*(p.c*q.d+p.d*q.c),
   p.a*q.c+p.c*q.a+2*(p.b*q.d+p.d*q.b),
   p.a*q.d+p.d*q.a+p.b*q.c+p.c*q.b⟩
noncomputable def Quad.eval (p : Quad) : ℝ :=
  p.a + p.b * Real.sqrt 2 + p.c * Real.sqrt 962 + p.d * (Real.sqrt 2 * Real.sqrt 962)

theorem Quad.eval_add (p q : Quad) : (p.add q).eval = p.eval + q.eval := by
  simp only [Quad.eval, Quad.add, Int.cast_add]
  ring

theorem Quad.eval_neg (p : Quad) : p.neg.eval = -p.eval := by
  simp only [Quad.eval, Quad.neg, Int.cast_neg]
  ring

theorem Quad.eval_mul (p q : Quad) : (p.mul q).eval = p.eval * q.eval := by
  have h2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have h962 : (Real.sqrt 962)^2 = 962 := Real.sq_sqrt (by norm_num)
  simp only [Quad.eval, Quad.mul, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
  ring_nf
  simp only [h2, h962]
  ring

instance : Zero Quad := ⟨⟨0,0,0,0⟩⟩
instance : One Quad := ⟨⟨1,0,0,0⟩⟩
instance : Add Quad := ⟨Quad.add⟩
instance : Neg Quad := ⟨Quad.neg⟩
instance : Mul Quad := ⟨Quad.mul⟩

def multiplyLinear {K : Type*} [Zero K] [Add K] [Mul K]
    (p : List K) (c l : K) : List K :=
  List.zipWith (· + ·) ((p.map (· * c)) ++ [0]) (0 :: p.map (· * l))

def evaluate {K : Type*} [Zero K] [Add K] [Mul K] (p : List K) (x : K) : K :=
  p.foldr (fun c r => r * x + c) 0

def eliminated {K : Type*} [Zero K] [Add K] [Mul K] [Neg K]
    (p : List K) (a : ℕ) (α x : K) : List K :=
  let state := ((p.take (a+1)).foldl
    (fun (s : K × K) c => (s.2, c + (α+x)*s.2 + -(α*x*s.1))) (0,0))
  [state.2, p[a+1]?.getD 0 + -(α*x*state.1)] ++ p.drop (a+2)

def numerator {K : Type*} [Zero K] [One K] [Add K] [Mul K] [Neg K]
    (α x c k : K) : K :=
  let A := multiplyLinear ((multiplyLinear · 1 x)^[30]
    ((multiplyLinear · α 1)^[52] [1])) k (-c)
  let B := multiplyLinear ((multiplyLinear · 1 1)^[30]
    ((multiplyLinear · x 1)^[52] [1])) c k
  let WA := eliminated A 52 α x
  let WB := eliminated B 52 α x
  evaluate WA x * evaluate WB 1 + -(evaluate WA 1 * evaluate WB x)

@[simp] theorem eval_zero : (0 : Quad).eval = 0 := by
  change (⟨0,0,0,0⟩ : Quad).eval = 0
  norm_num [Quad.eval]
@[simp] theorem eval_one : (1 : Quad).eval = 1 := by
  change (⟨1,0,0,0⟩ : Quad).eval = 1
  norm_num [Quad.eval]
@[simp] theorem eval_add (p q : Quad) : (p+q).eval = p.eval+q.eval := Quad.eval_add p q
@[simp] theorem eval_mul (p q : Quad) : (p*q).eval = p.eval*q.eval := Quad.eval_mul p q
@[simp] theorem eval_neg (p : Quad) : (-p).eval = -p.eval := Quad.eval_neg p

theorem map_linear (p : List Quad) (c l : Quad) :
    (multiplyLinear p c l).map Quad.eval = multiplyLinear (p.map Quad.eval) c.eval l.eval := by
  unfold multiplyLinear
  rw [List.map_zipWith]
  simp only [← List.zipWith_map, List.map_append, List.map_cons, List.map_nil,
    List.map_map, Function.comp_def, eval_zero, eval_mul, eval_add]

theorem map_evaluate (p : List Quad) (x : Quad) :
    (evaluate p x).eval = evaluate (p.map Quad.eval) x.eval := by
  induction p with
  | nil => simp [evaluate]
  | cons c p ih => simpa [evaluate] using congrArg (fun t => t * x.eval + c.eval) ih

private theorem map_state (p : List Quad) (s : Quad × Quad) (α x : Quad) :
    let q := p.foldl (fun s c => (s.2, c + (α+x)*s.2 + -(α*x*s.1))) s
    (q.1.eval, q.2.eval) =
    (p.map Quad.eval).foldl (fun s c => (s.2, c + (α.eval+x.eval)*s.2 + -(α.eval*x.eval*s.1))) (s.1.eval,s.2.eval) := by
  induction p generalizing s with
  | nil => rfl
  | cons c p ih => simpa using ih (s.2, c + (α+x)*s.2 + -(α*x*s.1))

theorem map_eliminated (p : List Quad) (a : ℕ) (α x : Quad) :
    (eliminated p a α x).map Quad.eval = eliminated (p.map Quad.eval) a α.eval x.eval := by
  have hs := map_state (p.take (a+1)) (0,0) α x
  simp only [eval_zero, List.map_take] at hs
  simp only [eliminated, List.map_append, List.map_cons, List.map_nil, List.map_drop]
  have h1 := congrArg Prod.fst hs
  have h2 := congrArg Prod.snd hs
  simp only [Prod.fst, Prod.snd] at h1 h2
  simp only [h1, h2, eval_add, eval_mul, eval_neg]
  congr 2
  simp only [List.getElem?_map]
  cases p[a+1]? <;> simp

theorem map_iterate_linear (n : ℕ) (p : List Quad) (c l : Quad) :
    (((multiplyLinear · c l)^[n]) p).map Quad.eval =
    ((multiplyLinear · c.eval l.eval)^[n]) (p.map Quad.eval) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', map_linear, ih]

theorem map_numerator (α x c k : Quad) :
    (numerator α x c k).eval = numerator α.eval x.eval c.eval k.eval := by
  simp only [numerator, eval_add, eval_mul, eval_neg, map_evaluate, map_eliminated,
    map_linear, map_iterate_linear, eval_one, List.map_cons, List.map_nil]

def computedQuad : Quad := numerator ⟨-31,0,1,0⟩ ⟨-1,1,0,0⟩ ⟨-1,0,1,0⟩ ⟨31,0,0,0⟩

end Atiyah.SingularCertificate

namespace Atiyah.SingularCertificate

def boundaryQuad : Quad := ⟨-27617676310841414184403890273801138211873358214292341411531145556687365825455268967567704150513817318114510318539359718037881998042143235352893445788797315616696192727714997982636746207257014192021442051222263688695892154887813022276837376, 19528646200011036930912885271781186982847508046334746073575687152879938128160181271082736019035570098777823525193524239103243410076928560205392613092904086266029097195607639472852164957534791256312981053469564204567324613936602198705561088, 890429621837309333180155374222157309305917183448595498707744960586690622839956151609225951964736231476318790761642681802326096161871361865363705113848374676904818781424840972901963794604206714536841969249976977091866670472723991495426560, -629628823770534549893206240437567385263214930004584778722682165536618877502041228759094228569914074617805570780919117145947652122616956696517541482446938465802333136063117260402723622609462291289728124516181422570486406009826006442799104⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem computedQuad_eq : computedQuad = boundaryQuad := by decide +kernel

theorem boundaryQuad_negative : boundaryQuad.eval < 0 := by
  have h2sq : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hrsq : (Real.sqrt 962)^2 = 962 := Real.sq_sqrt (by norm_num)
  have hpsq : (Real.sqrt 1924)^2 = 1924 := Real.sq_sqrt (by norm_num)
  have hp : Real.sqrt 2 * Real.sqrt 962 = Real.sqrt 1924 := by rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]; norm_num
  have h2 : Real.sqrt 2 ≤ (254232201230729256732104056844456770219098678726555547337425548242410227765672770491158596428559912855782789358954264268587831613869672521262735991984271646877739753852491184544053073323946127811396021713081366410839527602228694470682941512697463749755666735691082088233671763793895614142684151230750162785430 : ℝ) / 179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474124377767893424865485276302219601246094119453082952085005768838150682342462881473913110540827237163350510684586298239947245938479716304835356329624224137216 := by
    have hn := Real.sqrt_nonneg (2:ℝ)
    nlinarith [sq_nonneg (Real.sqrt 2 - (254232201230729256732104056844456770219098678726555547337425548242410227765672770491158596428559912855782789358954264268587831613869672521262735991984271646877739753852491184544053073323946127811396021713081366410839527602228694470682941512697463749755666735691082088233671763793895614142684151230750162785430:ℝ)/179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474124377767893424865485276302219601246094119453082952085005768838150682342462881473913110540827237163350510684586298239947245938479716304835356329624224137216)]
  have hr : Real.sqrt 962 ≤ (5575747469227887209415848348411378803228295876106769127174972956335857214591471171643349993479113165064547134769096533481913640467211171886326516221811252527688499210368131814318690131659510307858332606175913479444099693139835958958876173073265432516103595460959841975465700583555019552865520147432738743829021 : ℝ) / 179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474124377767893424865485276302219601246094119453082952085005768838150682342462881473913110540827237163350510684586298239947245938479716304835356329624224137216 := by
    have hn := Real.sqrt_nonneg (962:ℝ)
    nlinarith [sq_nonneg (Real.sqrt 962 - (5575747469227887209415848348411378803228295876106769127174972956335857214591471171643349993479113165064547134769096533481913640467211171886326516221811252527688499210368131814318690131659510307858332606175913479444099693139835958958876173073265432516103595460959841975465700583555019552865520147432738743829021:ℝ)/179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474124377767893424865485276302219601246094119453082952085005768838150682342462881473913110540827237163350510684586298239947245938479716304835356329624224137216)]
  have hpbound : (7885297691349539534299697808515022743175360365529543439671731139210567148532487594774116677152573553625092607468038067294611648968429399709382072609317173192446307065796153071497562870468161255981485721602055633176753209811873347333652321191417861711774633580930401734193088322039267729527528859146689011281464 : ℝ) / 179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474124377767893424865485276302219601246094119453082952085005768838150682342462881473913110540827237163350510684586298239947245938479716304835356329624224137216 ≤ Real.sqrt 1924 := by
    have hn := Real.sqrt_nonneg (1924:ℝ)
    nlinarith [sq_nonneg (Real.sqrt 1924 - (7885297691349539534299697808515022743175360365529543439671731139210567148532487594774116677152573553625092607468038067294611648968429399709382072609317173192446307065796153071497562870468161255981485721602055633176753209811873347333652321191417861711774633580930401734193088322039267729527528859146689011281464:ℝ)/179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474124377767893424865485276302219601246094119453082952085005768838150682342462881473913110540827237163350510684586298239947245938479716304835356329624224137216)]
  unfold Quad.eval boundaryQuad
  rw [hp]
  norm_num only [Int.cast_neg, Int.cast_ofNat]
  nlinarith only [h2, hr, hpbound]

/-- Kernel-checked negative numerator of the scaled 84-point boundary formula.
This is an arithmetic theorem, not a configuration or determinant identification. -/
theorem boundary_numerator_negative :
    numerator (Real.sqrt 962 - 31) (Real.sqrt 2 - 1) (Real.sqrt 962 - 1) (31 : ℝ) < 0 := by
  have h := boundaryQuad_negative
  rw [← computedQuad_eq] at h
  unfold computedQuad at h
  rw [map_numerator] at h
  have ha : (⟨-31,0,1,0⟩ : Quad).eval = Real.sqrt 962 - 31 := by norm_num [Quad.eval]; ring
  have hx : (⟨-1,1,0,0⟩ : Quad).eval = Real.sqrt 2 - 1 := by norm_num [Quad.eval]; ring
  have hc : (⟨-1,0,1,0⟩ : Quad).eval = Real.sqrt 962 - 1 := by norm_num [Quad.eval]; ring
  have hk : (⟨31,0,0,0⟩ : Quad).eval = 31 := by norm_num [Quad.eval]
  simpa only [ha, hx, hc, hk] using h

end Atiyah.SingularCertificate
