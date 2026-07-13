{-# LANGUAGE StrictData #-}

-- | Dubins chase — deck 0 dynamics for the Isaacs pursuit–evasion game
-- (classically: /homicidal chauffeur/).
--
-- = Players
--
-- * __Pursuer__ — Dubins car: fixed speed 'pSpeed', min turn radius 'pTurnR'.
--   Control \(u \in [-1,1]\) selects signed curvature \(u / R\).
-- * __Evader__ — simple motion: fixed speed 'eSpeed', free heading \(\phi\).
--
-- = Decks
--
-- * __0__ — pure Euler steps + absolute rollout; kinematic sanity oracles.
-- * __1__ — soft-capture loss through the rollout; finite-difference gradients
--   w.r.t. pursuer controls (evader open-loop fixed).  DiffP / polymorphic
--   Diff carrier is deck 1b once this FD oracle is boring.
--
-- Classical name retained only as literature keyword; working name is the
-- dynamics: /dubins-chase/.
module Circuit.AD.DubinsChase
  ( -- * Parameters
    Params (..),
    defaultParams,

    -- * State
    Pose2,
    Pos2,
    World,

    -- * Steps
    clampU,
    dubinsStep,
    simpleStep,
    stepWorld,

    -- * Geometry
    distance,
    captured,

    -- * Rollout
    rollout,
    pursuerPath,
    evaderPath,

    -- * Soft capture + FD gradients (deck 1)
    softGap,
    softLossWorld,
    softLossPath,
    lossOfControls,
    gradU_FD,
    descendU,
  )
where

-- | Game parameters (SI-ish units; scale free for toy oracles).
data Params = Params
  { -- | Pursuer speed \(v_p > 0\).
    pSpeed :: Double,
    -- | Evader speed \(v_e \ge 0\) (usually \(v_e < v_p\)).
    eSpeed :: Double,
    -- | Pursuer minimum turn radius \(R > 0\).
    pTurnR :: Double,
    -- | Capture radius \(\ell \ge 0\).
    captureR :: Double
  }
  deriving (Eq, Show)

-- | Default toy: pursuer twice as fast as evader, unit turn radius, capture 0.1.
defaultParams :: Params
defaultParams =
  Params
    { pSpeed = 1.0,
      eSpeed = 0.5,
      pTurnR = 1.0,
      captureR = 0.1
    }

-- | Pursuer pose: \((x, y, \theta)\) with \(\theta\) heading (radians, CCW from +x).
type Pose2 = (Double, Double, Double)

-- | Planar position.
type Pos2 = (Double, Double)

-- | Absolute world: pursuer pose + evader position.
type World = (Pose2, Pos2)

-- | Clamp pursuer control to \([-1,1]\).
clampU :: Double -> Double
clampU u = max (-1) (min 1 u)

-- | One Euler step of a Dubins car.
--
-- \[
--   \dot x = v \cos\theta,\quad
--   \dot y = v \sin\theta,\quad
--   \dot\theta = v \cdot u / R
-- \]
-- with \(u \in [-1,1]\) and curvature bound \(1/R\).
dubinsStep :: Params -> Double -> Double -> Pose2 -> Pose2
dubinsStep p dt u (x, y, th) =
  let v = pSpeed p
      r = pTurnR p
      u' = clampU u
      w = v * u' / r -- angular rate
      th' = th + w * dt
      x' = x + v * cos th * dt
      y' = y + v * sin th * dt
   in (x', y', th')

-- | One Euler step of simple motion at heading \(\phi\) (radians).
simpleStep :: Params -> Double -> Double -> Pos2 -> Pos2
simpleStep p dt phi (x, y) =
  let v = eSpeed p
   in (x + v * cos phi * dt, y + v * sin phi * dt)

-- | Joint absolute step.  Pursuer control \(u\), evader heading \(\phi\).
stepWorld :: Params -> Double -> Double -> Double -> World -> World
stepWorld p dt u phi (pr, ev) =
  (dubinsStep p dt u pr, simpleStep p dt phi ev)

-- | Euclidean distance between positions.
distance :: Pos2 -> Pos2 -> Double
distance (x0, y0) (x1, y1) =
  let dx = x1 - x0
      dy = y1 - y0
   in sqrt (dx * dx + dy * dy)

-- | Hard capture: distance \(\le \ell\).
captured :: Params -> Pos2 -> Pos2 -> Bool
captured p a b = distance a b <= captureR p

-- | Absolute rollout from initial world.
--
-- @controls@ is a list of @(u, phi)@ pairs, one per step of size @dt@.
rollout :: Params -> Double -> [(Double, Double)] -> World -> [World]
rollout p dt controls w0 = scanl step w0 controls
  where
    step w (u, phi) = stepWorld p dt u phi w

-- | Pursuer \((x,y)\) samples along a rollout.
pursuerPath :: [World] -> [Pos2]
pursuerPath = map (\( (x, y, _), _ ) -> (x, y))

-- | Evader samples along a rollout.
evaderPath :: [World] -> [Pos2]
evaderPath = map (\(_, e) -> e)

----------------------------------------------------------------------
-- Deck 1 — soft capture + FD through rollout
----------------------------------------------------------------------

-- | Soft gap: \(d - \ell\) (positive = still outside capture).
softGap :: Params -> Pos2 -> Pos2 -> Double
softGap p a b = distance a b - captureR p

-- | Smooth loss on one world state: \(\tfrac12 \max(0, d-\ell)^2\).
--
-- Zero inside the capture disk; quadratic outside.  Differentiable almost
-- everywhere (kink only on the capture boundary).
softLossWorld :: Params -> World -> Double
softLossWorld p ((xp, yp, _), e) =
  let g = softGap p (xp, yp) e
      g' = max 0 g
   in 0.5 * g' * g'

-- | Path loss: mean soft loss over the rollout (including the initial state).
softLossPath :: Params -> [World] -> Double
softLossPath p ws =
  let n = fromIntegral (length ws)
   in if n == 0 then 0 else sum (map (softLossWorld p) ws) / n

-- | Loss of a pursuer control sequence against a fixed open-loop evader.
--
-- @us@ — pursuer \(u_t \in [-1,1]\).
-- @phis@ — evader headings (same length as @us@).
lossOfControls :: Params -> Double -> [Double] -> [Double] -> World -> Double
lossOfControls p dt us phis w0 =
  let controls = zip us phis
      path = rollout p dt controls w0
   in softLossPath p path

-- | Central finite-difference gradient of 'lossOfControls' w.r.t. each \(u_t\).
--
-- Evader headings and initial world held fixed.  Oracle for reverse-mode /
-- DiffP once deck 1b lands.
gradU_FD :: Params -> Double -> Double -> [Double] -> [Double] -> World -> [Double]
gradU_FD p dt eps us phis w0 =
  [ (lossOfControls p dt (bump i eps) phis w0 - lossOfControls p dt (bump i (-eps)) phis w0)
      / (2 * eps)
  | i <- [0 .. length us - 1]
  ]
  where
    bump i e =
      [ if j == i then clampU (u + e) else u
      | (j, u) <- zip [0 ..] us
      ]

-- | One projected gradient step on pursuer controls (evader fixed).
--
-- \[
--   u \leftarrow \mathrm{clip}_{[-1,1]}(u - \eta \cdot \widehat{\nabla} u)
-- \]
-- with \(\widehat{\nabla}\) from 'gradU_FD'.
descendU :: Params -> Double -> Double -> Double -> [Double] -> [Double] -> World -> [Double]
descendU p dt eps eta us phis w0 =
  let g = gradU_FD p dt eps us phis w0
   in zipWith (\u gi -> clampU (u - eta * gi)) us g
