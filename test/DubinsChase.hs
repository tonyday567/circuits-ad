-- | Oracles for 'Circuit.AD.DubinsChase' (deck 0 kinematics + deck 1 soft loss / FD).
--
-- No book holdouts — runner opens those later.
module DubinsChase
  ( runDubinsChase,
  )
where

import Circuit.AD.DubinsChase
import Text.Printf (printf)

assertNear :: String -> Double -> Double -> Double -> IO ()
assertNear name tol got expected =
  if abs (got - expected) < tol
    then putStrLn $ "  PASS " ++ name ++ ": " ++ show got ++ " ≈ " ++ show expected
    else
      putStrLn $
        "  FAIL "
          ++ name
          ++ ": got "
          ++ show got
          ++ ", expected "
          ++ show expected

assertTrue :: String -> Bool -> IO ()
assertTrue name ok =
  if ok
    then putStrLn $ "  PASS " ++ name
    else putStrLn $ "  FAIL " ++ name

runDubinsChase :: IO ()
runDubinsChase = do
  putStrLn "=== dubins-chase deck 0: dynamics sanity ==="
  let p = defaultParams
      dt = 0.01
      tEnd = 1.0
      n = round (tEnd / dt) :: Int

  -- Straight line: u = 0, heading 0 → distance ≈ v_p * T
  let straight = rollout p dt (replicate n (0, 0)) ((0, 0, 0), (10, 0))
      (xf, yf, _) = fst (last straight)
      dStraight = sqrt (xf * xf + yf * yf)
  printf "straight: final pursuer (%.4f, %.4f) dist=%.4f\n" xf yf dStraight
  assertNear "straight-line path length" 0.02 dStraight (pSpeed p * tEnd)
  assertNear "straight no lateral drift" 1e-9 yf 0

  -- Full lock left: u = 1 → circle radius R, arc angle v*T/R
  let circ = rollout p dt (replicate n (1, 0)) ((0, 0, 0), (0, 0))
      samples = pursuerPath circ
      -- chord from start to end of arc
      (xe, ye) = last samples
      chord = sqrt (xe * xe + ye * ye)
      r = pTurnR p
      ang = pSpeed p * tEnd / r
      -- exact chord for circular arc of angle ang
      chordExact = 2 * r * sin (ang / 2)
  printf "full-lock: chord=%.4f exact=%.4f angle=%.4f rad\n" chord chordExact ang
  assertNear "full-lock turn chord" 0.05 chord chordExact

  -- Capture predicate
  assertTrue "captured at contact" (captured p (0, 0) (0.05, 0))
  assertTrue "not captured far" (not (captured p (0, 0) (1, 0)))

  -- Pure pursuit toward a fixed (stationary) evader: distance shrinks.
  let e0 = (1.0, 0.0)
      pStill = p {eSpeed = 0}
      chase =
        take (n + 1) $
          iterate
            ( \w ->
                let ((px, py, th), (ex, ey)) = w
                    phi = atan2 (ey - py) (ex - px)
                    err = atan2 (sin (phi - th)) (cos (phi - th))
                    u = max (-1) (min 1 (2 * err))
                 in stepWorld pStill dt u 0 w
            )
            ((0, 0, 0), e0)
      d0 = distance (0, 0) e0
      d1 = distance (let (a, b, _) = fst (last chase) in (a, b)) e0
  printf "chase fixed evader: d0=%.4f d1=%.4f\n" d0 d1
  assertTrue "distance decreases toward fixed evader" (d1 < d0 - 0.1)

  putStrLn "=== dubins-chase deck 1: soft loss + FD ==="
  -- Evader flees along +y; pursuer starts offset, open-loop zero controls
  -- should leave a positive soft loss; a short descent should reduce it.
  let wChase = ((0, 0, pi / 2), (0.5, 0)) -- pursuer facing +y, evader to the right
      phis = replicate 40 0 -- evader heads +x
      us0 = replicate 40 0 -- pursuer no turn
      loss0 = lossOfControls p dt us0 phis wChase
      g = gradU_FD p dt 1e-4 us0 phis wChase
      us1 = descendU p dt 1e-4 0.5 us0 phis wChase
      loss1 = lossOfControls p dt us1 phis wChase
  printf "soft loss0=%.6f  loss1=%.6f  |grad|_inf=%.4f\n" loss0 loss1 (maximum (map abs g))
  assertTrue "initial soft loss positive" (loss0 > 1e-3)
  assertTrue "FD grad has some signal" (maximum (map abs g) > 1e-6)
  assertTrue "one descent step reduces soft loss" (loss1 < loss0)

  -- Finite-difference self-consistency: bump one control, directional
  -- derivative ≈ central FD (same formula, different index).
  let usMid = 0 : replicate 39 0
      gMid = gradU_FD p dt 1e-4 usMid phis wChase
      dir = head gMid
      lossPlus = lossOfControls p dt (clampU (1e-3) : drop 1 usMid) phis wChase
      lossMinus = lossOfControls p dt (clampU (-1e-3) : drop 1 usMid) phis wChase
      dirFD = (lossPlus - lossMinus) / (2e-3)
  printf "grad_0=%.6f  re-FD=%.6f\n" dir dirFD
  assertNear "FD self-consistency on u0" 5e-2 dir dirFD

  putStrLn "=== dubins-chase deck 0+1 done ==="
