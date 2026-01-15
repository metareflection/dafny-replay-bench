// === Inlined from ../kernels/Replay.dfy ===
abstract module {:compile false} Domain {
  type Model
  type Action

  ghost predicate Inv(m: Model)

  function Init(): Model
  function Apply(m: Model, a: Action): Model
    requires Inv(m)
  function Normalize(m: Model): Model

  lemma InitSatisfiesInv()
    ensures Inv(Init())

  lemma StepPreservesInv(m: Model, a: Action)
    requires Inv(m)
    ensures Inv(Normalize(Apply(m,a)))
}

abstract module {:compile false} Kernel {
  import D : Domain

  function Step(m: D.Model, a: D.Action): D.Model
  requires D.Inv(m)
  {
    D.Normalize(D.Apply(m, a))
  }

  function InitHistory(): History {
    History([], D.Init(), [])
  }

  datatype History =
    History(past: seq<D.Model>, present: D.Model, future: seq<D.Model>)

  function Do(h: History, a: D.Action): History
  requires D.Inv(h.present)
  {
    History(h.past + [h.present], Step(h.present, a), [])
  }

  // Apply action without recording to history (for live preview during drag)
  function Preview(h: History, a: D.Action): History
  requires D.Inv(h.present)
  {
    History(h.past, Step(h.present, a), h.future)
  }

  // Commit current state, recording baseline to history (for end of drag)
  function CommitFrom(h: History, baseline: D.Model): History {
    History(h.past + [baseline], h.present, [])
  }

  function Undo(h: History): History {
    if |h.past| == 0 then h
    else
      var i := |h.past| - 1;
      History(h.past[..i], h.past[i], [h.present] + h.future)
  }

  function Redo(h: History): History {
    if |h.future| == 0 then h
    else
      History(h.past + [h.present], h.future[0], h.future[1..])
  }

  lemma DoPreservesInv(h: History, a: D.Action)
    requires D.Inv(h.present)
    ensures  D.Inv(Do(h, a).present)
  {
  }

  ghost predicate HistInv(h: History) {
    (forall i | 0 <= i < |h.past| :: D.Inv(h.past[i])) &&
    D.Inv(h.present) &&
    (forall j | 0 <= j < |h.future| :: D.Inv(h.future[j]))
  }

  lemma InitHistorySatisfiesInv()
    ensures HistInv(InitHistory())
  {
  }

  lemma UndoPreservesHistInv(h: History)
    requires HistInv(h)
    ensures  HistInv(Undo(h))
  {
  }

  lemma RedoPreservesHistInv(h: History)
    requires HistInv(h)
    ensures  HistInv(Redo(h))
  {
  }

  lemma DoPreservesHistInv(h: History, a: D.Action)
    requires HistInv(h)
    ensures  HistInv(Do(h, a))
  {
  }

  lemma PreviewPreservesHistInv(h: History, a: D.Action)
    requires HistInv(h)
    ensures  HistInv(Preview(h, a))
  {
  }

  lemma CommitFromPreservesHistInv(h: History, baseline: D.Model)
    requires HistInv(h)
    requires D.Inv(baseline)
    ensures  HistInv(CommitFrom(h, baseline))
  {
  }

  // proxy for linear undo: after a new action, there is no redo branch
  lemma DoHasNoRedoBranch(h: History, a: D.Action)
  requires HistInv(h)
  ensures Redo(Do(h, a)) == Do(h, a)
  {
  }
  // round-tripping properties
  lemma UndoRedoRoundTrip(h: History)
  requires |h.past| > 0
  ensures Redo(Undo(h)) == h
  {
  }
  lemma RedoUndoRoundTrip(h: History)
  requires |h.future| > 0
  ensures Undo(Redo(h)) == h
  {
  }
  // idempotence at boundaries
  lemma UndoAtBeginningIsNoOp(h: History)
  requires |h.past| == 0
  ensures Undo(h) == h
  {
  }
  lemma RedoAtEndIsNoOp(h: History)
  requires |h.future| == 0
  ensures Redo(h) == h
  {
  }
}

// === End ../kernels/Replay.dfy ===
// === Inlined from ColorWheelSpec.dfy ===
// ColorWheel Domain Specification
// A verified color palette generator with mood + harmony constraints

module ColorWheelSpec {

  // ============================================================================
  // Core Types
  // ============================================================================

  datatype Color = Color(h: int, s: int, l: int)

  datatype Mood =
    | Vibrant      // S ≥ 70,  40 ≤ L ≤ 60
    | SoftMuted    // 20 ≤ S ≤ 45, 55 ≤ L ≤ 75
    | Pastel       // S ≤ 35,  L ≥ 75
    | DeepJewel    // S ≥ 60,  25 ≤ L ≤ 45
    | Earth        // 15 ≤ S ≤ 40, 30 ≤ L ≤ 60
    | Neon         // S ≥ 90,  50 ≤ L ≤ 65
    | Custom       // No S/L constraints

  datatype Harmony =
    | Complementary     // 2 base hues: [H₀, H₀+180°] + 3 variations
    | Triadic           // 3 base hues: [H₀, H₀+120°, H₀+240°] + 2 variations
    | Analogous         // 5 hues: [H₀-30°, H₀-15°, H₀, H₀+15°, H₀+30°]
    | SplitComplement   // 3 base hues: [H₀, H₀+150°, H₀+210°] + 2 variations
    | Square            // 4 base hues: [H₀, H₀+90°, H₀+180°, H₀+270°] + 1 variation
    | Custom            // No hue relationship

  datatype Model = Model(
    baseHue: int,                    // 0-359, the anchor hue
    mood: Mood,
    harmony: Harmony,
    colors: seq<Color>,              // Always exactly 5 colors
    contrastPair: (int, int),        // (foreground index, background index)
    // Cumulative palette adjustments (for UI slider display)
    adjustmentH: int,                // Cumulative hue adjustment
    adjustmentS: int,                // Cumulative saturation adjustment
    adjustmentL: int                 // Cumulative lightness adjustment
  )

  datatype Action =
    // randomSeeds: 10 values [0-100] for random S/L generation (2 per color)
    | GeneratePalette(baseHue: int, mood: Mood, harmony: Harmony, randomSeeds: seq<int>)
    | AdjustColor(index: int, deltaH: int, deltaS: int, deltaL: int)
    // AdjustPalette: Applies linked adjustment to ALL colors
    | AdjustPalette(deltaH: int, deltaS: int, deltaL: int)
    | SelectContrastPair(fg: int, bg: int)
    | SetColorDirect(index: int, color: Color)
    // randomSeeds: 10 values for regenerating colors with new mood
    | RegenerateMood(mood: Mood, randomSeeds: seq<int>)
    // randomSeeds: 10 values for regenerating colors with new harmony
    | RegenerateHarmony(harmony: Harmony, randomSeeds: seq<int>)
    // newBaseHue + randomSeeds: pick new base, regenerate
    | RandomizeBaseHue(newBaseHue: int, randomSeeds: seq<int>)

  // ============================================================================
  // Helper Functions
  // ============================================================================

  function Clamp(x: int, min: int, max: int): int {
    if x < min then min
    else if x > max then max
    else x
  }

  function NormalizeHue(h: int): int {
    var normalized := h % 360;
    if normalized < 0 then normalized + 360 else normalized
  }

  function ClampColor(c: Color): Color {
    Color(
      NormalizeHue(c.h),
      Clamp(c.s, 0, 100),
      Clamp(c.l, 0, 100)
    )
  }

  // ============================================================================
  // Mood Predicates
  // ============================================================================

  predicate ValidColor(c: Color) {
    0 <= c.h < 360 && 0 <= c.s <= 100 && 0 <= c.l <= 100
  }

  predicate ValidBaseHue(h: int) {
    0 <= h < 360
  }

  predicate ColorSatisfiesMood(c: Color, mood: Mood) {
    match mood
    case Vibrant    => c.s >= 70 && 40 <= c.l <= 60
    case SoftMuted  => 20 <= c.s <= 45 && 55 <= c.l <= 75
    case Pastel     => c.s <= 35 && c.l >= 75
    case DeepJewel  => c.s >= 60 && 25 <= c.l <= 45
    case Earth      => 15 <= c.s <= 40 && 30 <= c.l <= 60
    case Neon       => c.s >= 90 && 50 <= c.l <= 65
    case Custom     => true
  }

  // Returns (minS, maxS, minL, maxL) bounds for a given mood
  function MoodBounds(mood: Mood): (int, int, int, int) {
    match mood
    case Vibrant    => (70, 100, 40, 60)
    case SoftMuted  => (20, 45, 55, 75)
    case Pastel     => (0, 35, 75, 100)
    case DeepJewel  => (60, 100, 25, 45)
    case Earth      => (15, 40, 30, 60)
    case Neon       => (90, 100, 50, 65)
    case Custom     => (0, 100, 0, 100)
  }

  // Map a random seed [0-100] to a value in [min, max]
  function RandomInRange(seed: int, min: int, max: int): int
    requires 0 <= seed <= 100
    requires min <= max
  {
    if min == max then min
    else min + (seed * (max - min)) / 100
  }

  // Generate random (S, L) within mood bounds using two random seeds
  function RandomSLForMood(mood: Mood, seedS: int, seedL: int): (int, int)
    requires 0 <= seedS <= 100
    requires 0 <= seedL <= 100
  {
    var (minS, maxS, minL, maxL) := MoodBounds(mood);
    (RandomInRange(seedS, minS, maxS), RandomInRange(seedL, minL, maxL))
  }

  // Golden ratio approximation * 100 = 61.8 ≈ 62
  // Golden ratio distribution avoids clustering and maximizes visual distinction
  const GoldenOffset: int := 62

  // Generate (S, L) using golden ratio distribution for maximum variance
  // Each color's position is offset by golden ratio, ensuring even distribution
  // and dramatic changes between regenerations
  function GoldenSLForMood(mood: Mood, colorIndex: int, seedS: int, seedL: int): (int, int)
    requires 0 <= colorIndex < 5
    requires 0 <= seedS <= 100
    requires 0 <= seedL <= 100
  {
    var (minS, maxS, minL, maxL) := MoodBounds(mood);

    // Golden ratio offset creates mathematically optimal distribution
    // Using different multipliers for S and L to avoid correlation
    var spreadS := (seedS + colorIndex * GoldenOffset) % 101;
    var spreadL := (seedL + colorIndex * 38) % 101;  // 38 ≈ 62 * 0.618 (nested golden)

    (RandomInRange(spreadS, minS, maxS), RandomInRange(spreadL, minL, maxL))
  }

  // ============================================================================
  // Harmony Functions
  // ============================================================================

  // Returns the base harmony hues (before padding to 5)
  function BaseHarmonyHues(baseHue: int, harmony: Harmony): seq<int> {
    match harmony
    case Complementary   => [baseHue, NormalizeHue(baseHue + 180)]
    case Triadic         => [baseHue, NormalizeHue(baseHue + 120), NormalizeHue(baseHue + 240)]
    case Analogous       => [NormalizeHue(baseHue - 30), NormalizeHue(baseHue - 15),
                             baseHue, NormalizeHue(baseHue + 15), NormalizeHue(baseHue + 30)]
    case SplitComplement => [baseHue, NormalizeHue(baseHue + 150), NormalizeHue(baseHue + 210)]
    case Square          => [baseHue, NormalizeHue(baseHue + 90),
                             NormalizeHue(baseHue + 180), NormalizeHue(baseHue + 270)]
    case Custom          => [] // No constraint
  }

  // Hue spread offset for creating variation in repeated hues
  // 35° provides better visual distinction than 20° while staying within harmony "feel"
  const HueSpread: int := 35

  // Returns all 5 hues for a harmony (with spreading for variety)
  // Instead of repeating exact hues, we spread them by ±HueSpread degrees
  function AllHarmonyHues(baseHue: int, harmony: Harmony): seq<int> {
    var base := BaseHarmonyHues(baseHue, harmony);
    if harmony == Harmony.Custom then []
    else if |base| == 5 then base  // Analogous: already 5 distinct hues
    else if |base| == 4 then
      // Square: add midpoint between first two hues
      base + [NormalizeHue(baseHue + 45)]
    else if |base| == 3 then
      // Triadic/Split: spread the first two base hues
      base + [NormalizeHue(base[0] + HueSpread), NormalizeHue(base[1] - HueSpread)]
    else if |base| == 2 then
      // Complementary: spread both base hues
      base + [NormalizeHue(base[0] + HueSpread),
              NormalizeHue(base[1] + HueSpread),
              NormalizeHue(base[0] - HueSpread)]
    else []
  }

  // Check if a color palette's hues match the expected harmony pattern
  predicate HuesMatchHarmony(colors: seq<Color>, baseHue: int, harmony: Harmony) {
    if harmony == Harmony.Custom then true
    else
      var expectedHues := AllHarmonyHues(baseHue, harmony);
      |colors| == 5 && |expectedHues| == 5 &&
      forall i | 0 <= i < 5 :: colors[i].h == expectedHues[i]
  }

  // ============================================================================
  // Main Invariant
  // ============================================================================

  predicate Inv(m: Model) {
    && ValidBaseHue(m.baseHue)
    && |m.colors| == 5
    && (forall i | 0 <= i < 5 :: ValidColor(m.colors[i]))
    && 0 <= m.contrastPair.0 < 5
    && 0 <= m.contrastPair.1 < 5
    // Mood constraint: all colors satisfy mood (unless Custom)
    && (m.mood != Mood.Custom ==>
          forall i | 0 <= i < 5 :: ColorSatisfiesMood(m.colors[i], m.mood))
    // Harmony constraint: hues follow harmony pattern (unless Custom)
    && HuesMatchHarmony(m.colors, m.baseHue, m.harmony)
  }

  // ============================================================================
  // Initial State
  // ============================================================================

  function Init(): Model {
    var randomSeeds := [50, 50, 50, 50, 50, 50, 50, 50, 50, 50];
    var baseHue := 180;  // Start with blue
    var mood := Vibrant;
    var harmony := Complementary;
    var colors := GeneratePaletteColors(baseHue, mood, harmony, randomSeeds);
    Model(baseHue, mood, harmony, colors, (0, 1), 0, 0, 0)
  }

  // ============================================================================
  // Color Generation
  // ============================================================================

  predicate ValidRandomSeeds(seeds: seq<int>) {
    |seeds| == 10 && (forall i | 0 <= i < 10 :: 0 <= seeds[i] <= 100)
  }

  // Check if all colors in a sequence satisfy a mood constraint
  predicate AllColorsSatisfyMood(colors: seq<Color>, mood: Mood)
    requires |colors| == 5
  {
    forall i | 0 <= i < 5 :: ColorSatisfiesMood(colors[i], mood)
  }

  // Generate a color with given hue using golden ratio S/L distribution
  function GenerateColorGolden(h: int, mood: Mood, colorIndex: int, seedS: int, seedL: int): Color
    requires 0 <= h < 360
    requires 0 <= colorIndex < 5
    requires 0 <= seedS <= 100
    requires 0 <= seedL <= 100
  {
    var (s, l) := GoldenSLForMood(mood, colorIndex, seedS, seedL);
    Color(h, s, l)
  }

  // Generate a full 5-color palette using golden ratio S/L distribution
  function GeneratePaletteColors(baseHue: int, mood: Mood, harmony: Harmony, randomSeeds: seq<int>): seq<Color>
    requires ValidBaseHue(baseHue)
    requires ValidRandomSeeds(randomSeeds)
  {
    var hues := AllHarmonyHues(baseHue, harmony);

    if |hues| != 5 then
      // Fallback for Custom harmony: use baseHue for all
      [GenerateColorGolden(baseHue, mood, 0, randomSeeds[0], randomSeeds[1]),
       GenerateColorGolden(baseHue, mood, 1, randomSeeds[2], randomSeeds[3]),
       GenerateColorGolden(baseHue, mood, 2, randomSeeds[4], randomSeeds[5]),
       GenerateColorGolden(baseHue, mood, 3, randomSeeds[6], randomSeeds[7]),
       GenerateColorGolden(baseHue, mood, 4, randomSeeds[8], randomSeeds[9])]
    else
      [GenerateColorGolden(hues[0], mood, 0, randomSeeds[0], randomSeeds[1]),
       GenerateColorGolden(hues[1], mood, 1, randomSeeds[2], randomSeeds[3]),
       GenerateColorGolden(hues[2], mood, 2, randomSeeds[4], randomSeeds[5]),
       GenerateColorGolden(hues[3], mood, 3, randomSeeds[6], randomSeeds[7]),
       GenerateColorGolden(hues[4], mood, 4, randomSeeds[8], randomSeeds[9])]
  }

  // ============================================================================
  // State Transitions (Apply)
  // ============================================================================

  function Apply(m: Model, a: Action): Model
  requires Inv(m)
  {
    match a
    case GeneratePalette(baseHue, mood, harmony, randomSeeds) =>
      if !ValidBaseHue(baseHue) || !ValidRandomSeeds(randomSeeds) then m
      else
        var colors := GeneratePaletteColors(baseHue, mood, harmony, randomSeeds);
        m.(baseHue := baseHue, mood := mood, harmony := harmony, colors := colors,
           adjustmentH := 0, adjustmentS := 0, adjustmentL := 0)

    case AdjustColor(index, deltaH, deltaS, deltaL) =>
      if index < 0 || index >= |m.colors| then m
      else
        ApplyIndependentAdjustment(m, index, deltaH, deltaS, deltaL)

    // AdjustPalette: Applies linked adjustment to all colors
    case AdjustPalette(deltaH, deltaS, deltaL) =>
      var adjusted := ApplyLinkedAdjustment(m, deltaH, deltaS, deltaL);
      adjusted.(adjustmentH := m.adjustmentH + deltaH,
                adjustmentS := m.adjustmentS + deltaS,
                adjustmentL := m.adjustmentL + deltaL)

    case SelectContrastPair(fg, bg) =>
      if 0 <= fg < 5 && 0 <= bg < 5 then
        m.(contrastPair := (fg, bg))
      else m

    case SetColorDirect(index, color) =>
      if index < 0 || index >= |m.colors| then m
      else
        ApplySetColorDirect(m, index, color)

    case RegenerateMood(mood, randomSeeds) =>
      if !ValidRandomSeeds(randomSeeds) then m
      else
        var colors := GeneratePaletteColors(m.baseHue, mood, m.harmony, randomSeeds);
        m.(mood := mood, colors := colors, adjustmentH := 0, adjustmentS := 0, adjustmentL := 0)

    case RegenerateHarmony(harmony, randomSeeds) =>
      if !ValidRandomSeeds(randomSeeds) then m
      else
        var colors := GeneratePaletteColors(m.baseHue, m.mood, harmony, randomSeeds);
        m.(harmony := harmony, colors := colors, adjustmentH := 0, adjustmentS := 0, adjustmentL := 0)

    case RandomizeBaseHue(newBaseHue, randomSeeds) =>
      if !ValidBaseHue(newBaseHue) || !ValidRandomSeeds(randomSeeds) then m
      else
        var colors := GeneratePaletteColors(newBaseHue, m.mood, m.harmony, randomSeeds);
        m.(baseHue := newBaseHue, colors := colors, adjustmentH := 0, adjustmentS := 0, adjustmentL := 0)
  }

  // ============================================================================
  // Linked Adjustment: Shift all colors together
  // ============================================================================

  function ApplyLinkedAdjustment(m: Model, deltaH: int, deltaS: int, deltaL: int): Model
    requires |m.colors| == 5
    requires forall i | 0 <= i < 5 :: ValidColor(m.colors[i])
  {
    // Shift baseHue and regenerate harmony hues
    var newBaseHue := NormalizeHue(m.baseHue + deltaH);
    var newHues := AllHarmonyHues(newBaseHue, m.harmony);

    // Adjust S and L for all colors, preserving hues
    var adjustedColors :=
      if |newHues| == 5 then
        [AdjustColorSL(m.colors[0], newHues[0], deltaS, deltaL),
         AdjustColorSL(m.colors[1], newHues[1], deltaS, deltaL),
         AdjustColorSL(m.colors[2], newHues[2], deltaS, deltaL),
         AdjustColorSL(m.colors[3], newHues[3], deltaS, deltaL),
         AdjustColorSL(m.colors[4], newHues[4], deltaS, deltaL)]
      else (
        // Custom harmony: shift each color's hue by deltaH, adjust S/L
        [AdjustColorSL(m.colors[0], NormalizeHue(m.colors[0].h + deltaH), deltaS, deltaL),
         AdjustColorSL(m.colors[1], NormalizeHue(m.colors[1].h + deltaH), deltaS, deltaL),
         AdjustColorSL(m.colors[2], NormalizeHue(m.colors[2].h + deltaH), deltaS, deltaL),
         AdjustColorSL(m.colors[3], NormalizeHue(m.colors[3].h + deltaH), deltaS, deltaL),
         AdjustColorSL(m.colors[4], NormalizeHue(m.colors[4].h + deltaH), deltaS, deltaL)]
      );

    // Check if any color breaks mood bounds
    var moodBroken := m.mood != Mood.Custom &&
                      exists i | 0 <= i < 5 :: !ColorSatisfiesMood(adjustedColors[i], m.mood);

    var newMood := if moodBroken then Mood.Custom else m.mood;

    m.(baseHue := newBaseHue, colors := adjustedColors, mood := newMood)
  }

  // Helper: Adjust a color's S and L while setting a specific hue
  function AdjustColorSL(c: Color, newHue: int, deltaS: int, deltaL: int): Color
    requires 0 <= newHue < 360
  {
    var newS := Clamp(c.s + deltaS, 0, 100);
    var newL := Clamp(c.l + deltaL, 0, 100);
    Color(newHue, newS, newL)
  }

  // ============================================================================
  // Independent Adjustment: Adjust only one color
  // ============================================================================

  function ApplyIndependentAdjustment(m: Model, index: int, deltaH: int, deltaS: int, deltaL: int): Model
    requires 0 <= index < 5
    requires |m.colors| == 5
  {
    var oldColor := m.colors[index];
    var newColor := ClampColor(Color(
      oldColor.h + deltaH,
      oldColor.s + deltaS,
      oldColor.l + deltaL
    ));

    // Check if hue changed and no longer matches harmony
    var expectedHues := AllHarmonyHues(m.baseHue, m.harmony);
    var hueChanged := |expectedHues| == 5 && newColor.h != expectedHues[index];
    var harmonyBroken := m.harmony != Harmony.Custom && hueChanged;

    // Check if mood bounds broken
    var moodBroken := m.mood != Mood.Custom && !ColorSatisfiesMood(newColor, m.mood);

    var newColors := m.colors[index := newColor];
    var newHarmony := if harmonyBroken then Harmony.Custom else m.harmony;
    var newMood := if moodBroken then Mood.Custom else m.mood;

    m.(colors := newColors, harmony := newHarmony, mood := newMood)
  }

  // ============================================================================
  // SetColorDirect: Try to preserve mood/harmony when possible
  // ============================================================================

  function ApplySetColorDirect(m: Model, index: int, color: Color): Model
    requires 0 <= index < 5
    requires |m.colors| == 5
  {
    var clampedColor := ClampColor(color);

    // Check if new color matches expected harmony hue
    var expectedHues := AllHarmonyHues(m.baseHue, m.harmony);
    var hueMatches := |expectedHues| == 5 && clampedColor.h == expectedHues[index];
    var harmonyPreserved := m.harmony == Harmony.Custom || hueMatches;

    // Check if new color satisfies current mood
    var moodPreserved := m.mood == Mood.Custom || ColorSatisfiesMood(clampedColor, m.mood);

    var newColors := m.colors[index := clampedColor];
    var newHarmony := if harmonyPreserved then m.harmony else Harmony.Custom;
    var newMood := if moodPreserved then m.mood else Mood.Custom;

    m.(colors := newColors, harmony := newHarmony, mood := newMood)
  }

  // ============================================================================
  // Normalize: Ensure invariant holds
  // ============================================================================

  function Normalize(m: Model): Model {
    // Ensure baseHue is in valid range
    var normalizedBaseHue := NormalizeHue(m.baseHue);

    // Ensure all colors are valid (clamped)
    // If we don't have exactly 5 colors, create defaults
    var normalizedColors :=
      if |m.colors| == 5 then [
        ClampColor(m.colors[0]),
        ClampColor(m.colors[1]),
        ClampColor(m.colors[2]),
        ClampColor(m.colors[3]),
        ClampColor(m.colors[4])
      ]
      else [
        Color(0, 0, 0),
        Color(0, 0, 0),
        Color(0, 0, 0),
        Color(0, 0, 0),
        Color(0, 0, 0)
      ];

    // Ensure contrast pair indices are valid
    var normalizedContrastPair :=
      if 0 <= m.contrastPair.0 < 5 && 0 <= m.contrastPair.1 < 5 then
        m.contrastPair
      else
        (0, 1);

    // If mood is not Custom, verify all colors satisfy it; otherwise switch to Custom
    var finalMood :=
      if m.mood == Mood.Custom then Mood.Custom
      else if AllColorsSatisfyMood(normalizedColors, m.mood) then m.mood
      else Mood.Custom;

    // If harmony is not Custom, verify hues match; otherwise switch to Custom
    var finalHarmony :=
      if m.harmony == Harmony.Custom then Harmony.Custom
      else if HuesMatchHarmony(normalizedColors, normalizedBaseHue, m.harmony) then m.harmony
      else Harmony.Custom;

    m.(
      baseHue := normalizedBaseHue,
      colors := normalizedColors,
      contrastPair := normalizedContrastPair,
      mood := finalMood,
      harmony := finalHarmony
    )
  }
}

// === End ColorWheelSpec.dfy ===
// === Inlined from ColorWheelProof.dfy ===
// === Inlined from ColorWheelSpec.dfy ===
// ColorWheel Domain Specification
// A verified color palette generator with mood + harmony constraints

module ColorWheelSpec {

  // ============================================================================
  // Core Types
  // ============================================================================

  datatype Color = Color(h: int, s: int, l: int)

  datatype Mood =
    | Vibrant      // S ≥ 70,  40 ≤ L ≤ 60
    | SoftMuted    // 20 ≤ S ≤ 45, 55 ≤ L ≤ 75
    | Pastel       // S ≤ 35,  L ≥ 75
    | DeepJewel    // S ≥ 60,  25 ≤ L ≤ 45
    | Earth        // 15 ≤ S ≤ 40, 30 ≤ L ≤ 60
    | Neon         // S ≥ 90,  50 ≤ L ≤ 65
    | Custom       // No S/L constraints

  datatype Harmony =
    | Complementary     // 2 base hues: [H₀, H₀+180°] + 3 variations
    | Triadic           // 3 base hues: [H₀, H₀+120°, H₀+240°] + 2 variations
    | Analogous         // 5 hues: [H₀-30°, H₀-15°, H₀, H₀+15°, H₀+30°]
    | SplitComplement   // 3 base hues: [H₀, H₀+150°, H₀+210°] + 2 variations
    | Square            // 4 base hues: [H₀, H₀+90°, H₀+180°, H₀+270°] + 1 variation
    | Custom            // No hue relationship

  datatype Model = Model(
    baseHue: int,                    // 0-359, the anchor hue
    mood: Mood,
    harmony: Harmony,
    colors: seq<Color>,              // Always exactly 5 colors
    contrastPair: (int, int),        // (foreground index, background index)
    // Cumulative palette adjustments (for UI slider display)
    adjustmentH: int,                // Cumulative hue adjustment
    adjustmentS: int,                // Cumulative saturation adjustment
    adjustmentL: int                 // Cumulative lightness adjustment
  )

  datatype Action =
    // randomSeeds: 10 values [0-100] for random S/L generation (2 per color)
    | GeneratePalette(baseHue: int, mood: Mood, harmony: Harmony, randomSeeds: seq<int>)
    | AdjustColor(index: int, deltaH: int, deltaS: int, deltaL: int)
    // AdjustPalette: Applies linked adjustment to ALL colors
    | AdjustPalette(deltaH: int, deltaS: int, deltaL: int)
    | SelectContrastPair(fg: int, bg: int)
    | SetColorDirect(index: int, color: Color)
    // randomSeeds: 10 values for regenerating colors with new mood
    | RegenerateMood(mood: Mood, randomSeeds: seq<int>)
    // randomSeeds: 10 values for regenerating colors with new harmony
    | RegenerateHarmony(harmony: Harmony, randomSeeds: seq<int>)
    // newBaseHue + randomSeeds: pick new base, regenerate
    | RandomizeBaseHue(newBaseHue: int, randomSeeds: seq<int>)

  // ============================================================================
  // Helper Functions
  // ============================================================================

  function Clamp(x: int, min: int, max: int): int {
    if x < min then min
    else if x > max then max
    else x
  }

  function NormalizeHue(h: int): int {
    var normalized := h % 360;
    if normalized < 0 then normalized + 360 else normalized
  }

  function ClampColor(c: Color): Color {
    Color(
      NormalizeHue(c.h),
      Clamp(c.s, 0, 100),
      Clamp(c.l, 0, 100)
    )
  }

  // ============================================================================
  // Mood Predicates
  // ============================================================================

  predicate ValidColor(c: Color) {
    0 <= c.h < 360 && 0 <= c.s <= 100 && 0 <= c.l <= 100
  }

  predicate ValidBaseHue(h: int) {
    0 <= h < 360
  }

  predicate ColorSatisfiesMood(c: Color, mood: Mood) {
    match mood
    case Vibrant    => c.s >= 70 && 40 <= c.l <= 60
    case SoftMuted  => 20 <= c.s <= 45 && 55 <= c.l <= 75
    case Pastel     => c.s <= 35 && c.l >= 75
    case DeepJewel  => c.s >= 60 && 25 <= c.l <= 45
    case Earth      => 15 <= c.s <= 40 && 30 <= c.l <= 60
    case Neon       => c.s >= 90 && 50 <= c.l <= 65
    case Custom     => true
  }

  // Returns (minS, maxS, minL, maxL) bounds for a given mood
  function MoodBounds(mood: Mood): (int, int, int, int) {
    match mood
    case Vibrant    => (70, 100, 40, 60)
    case SoftMuted  => (20, 45, 55, 75)
    case Pastel     => (0, 35, 75, 100)
    case DeepJewel  => (60, 100, 25, 45)
    case Earth      => (15, 40, 30, 60)
    case Neon       => (90, 100, 50, 65)
    case Custom     => (0, 100, 0, 100)
  }

  // Map a random seed [0-100] to a value in [min, max]
  function RandomInRange(seed: int, min: int, max: int): int
    requires 0 <= seed <= 100
    requires min <= max
  {
    if min == max then min
    else min + (seed * (max - min)) / 100
  }

  // Generate random (S, L) within mood bounds using two random seeds
  function RandomSLForMood(mood: Mood, seedS: int, seedL: int): (int, int)
    requires 0 <= seedS <= 100
    requires 0 <= seedL <= 100
  {
    var (minS, maxS, minL, maxL) := MoodBounds(mood);
    (RandomInRange(seedS, minS, maxS), RandomInRange(seedL, minL, maxL))
  }

  // Golden ratio approximation * 100 = 61.8 ≈ 62
  // Golden ratio distribution avoids clustering and maximizes visual distinction
  const GoldenOffset: int := 62

  // Generate (S, L) using golden ratio distribution for maximum variance
  // Each color's position is offset by golden ratio, ensuring even distribution
  // and dramatic changes between regenerations
  function GoldenSLForMood(mood: Mood, colorIndex: int, seedS: int, seedL: int): (int, int)
    requires 0 <= colorIndex < 5
    requires 0 <= seedS <= 100
    requires 0 <= seedL <= 100
  {
    var (minS, maxS, minL, maxL) := MoodBounds(mood);

    // Golden ratio offset creates mathematically optimal distribution
    // Using different multipliers for S and L to avoid correlation
    var spreadS := (seedS + colorIndex * GoldenOffset) % 101;
    var spreadL := (seedL + colorIndex * 38) % 101;  // 38 ≈ 62 * 0.618 (nested golden)

    (RandomInRange(spreadS, minS, maxS), RandomInRange(spreadL, minL, maxL))
  }

  // ============================================================================
  // Harmony Functions
  // ============================================================================

  // Returns the base harmony hues (before padding to 5)
  function BaseHarmonyHues(baseHue: int, harmony: Harmony): seq<int> {
    match harmony
    case Complementary   => [baseHue, NormalizeHue(baseHue + 180)]
    case Triadic         => [baseHue, NormalizeHue(baseHue + 120), NormalizeHue(baseHue + 240)]
    case Analogous       => [NormalizeHue(baseHue - 30), NormalizeHue(baseHue - 15),
                             baseHue, NormalizeHue(baseHue + 15), NormalizeHue(baseHue + 30)]
    case SplitComplement => [baseHue, NormalizeHue(baseHue + 150), NormalizeHue(baseHue + 210)]
    case Square          => [baseHue, NormalizeHue(baseHue + 90),
                             NormalizeHue(baseHue + 180), NormalizeHue(baseHue + 270)]
    case Custom          => [] // No constraint
  }

  // Hue spread offset for creating variation in repeated hues
  // 35° provides better visual distinction than 20° while staying within harmony "feel"
  const HueSpread: int := 35

  // Returns all 5 hues for a harmony (with spreading for variety)
  // Instead of repeating exact hues, we spread them by ±HueSpread degrees
  function AllHarmonyHues(baseHue: int, harmony: Harmony): seq<int> {
    var base := BaseHarmonyHues(baseHue, harmony);
    if harmony == Harmony.Custom then []
    else if |base| == 5 then base  // Analogous: already 5 distinct hues
    else if |base| == 4 then
      // Square: add midpoint between first two hues
      base + [NormalizeHue(baseHue + 45)]
    else if |base| == 3 then
      // Triadic/Split: spread the first two base hues
      base + [NormalizeHue(base[0] + HueSpread), NormalizeHue(base[1] - HueSpread)]
    else if |base| == 2 then
      // Complementary: spread both base hues
      base + [NormalizeHue(base[0] + HueSpread),
              NormalizeHue(base[1] + HueSpread),
              NormalizeHue(base[0] - HueSpread)]
    else []
  }

  // Check if a color palette's hues match the expected harmony pattern
  predicate HuesMatchHarmony(colors: seq<Color>, baseHue: int, harmony: Harmony) {
    if harmony == Harmony.Custom then true
    else
      var expectedHues := AllHarmonyHues(baseHue, harmony);
      |colors| == 5 && |expectedHues| == 5 &&
      forall i | 0 <= i < 5 :: colors[i].h == expectedHues[i]
  }

  // ============================================================================
  // Main Invariant
  // ============================================================================

  predicate Inv(m: Model) {
    && ValidBaseHue(m.baseHue)
    && |m.colors| == 5
    && (forall i | 0 <= i < 5 :: ValidColor(m.colors[i]))
    && 0 <= m.contrastPair.0 < 5
    && 0 <= m.contrastPair.1 < 5
    // Mood constraint: all colors satisfy mood (unless Custom)
    && (m.mood != Mood.Custom ==>
          forall i | 0 <= i < 5 :: ColorSatisfiesMood(m.colors[i], m.mood))
    // Harmony constraint: hues follow harmony pattern (unless Custom)
    && HuesMatchHarmony(m.colors, m.baseHue, m.harmony)
  }

  // ============================================================================
  // Initial State
  // ============================================================================

  function Init(): Model {
    var randomSeeds := [50, 50, 50, 50, 50, 50, 50, 50, 50, 50];
    var baseHue := 180;  // Start with blue
    var mood := Vibrant;
    var harmony := Complementary;
    var colors := GeneratePaletteColors(baseHue, mood, harmony, randomSeeds);
    Model(baseHue, mood, harmony, colors, (0, 1), 0, 0, 0)
  }

  // ============================================================================
  // Color Generation
  // ============================================================================

  predicate ValidRandomSeeds(seeds: seq<int>) {
    |seeds| == 10 && (forall i | 0 <= i < 10 :: 0 <= seeds[i] <= 100)
  }

  // Check if all colors in a sequence satisfy a mood constraint
  predicate AllColorsSatisfyMood(colors: seq<Color>, mood: Mood)
    requires |colors| == 5
  {
    forall i | 0 <= i < 5 :: ColorSatisfiesMood(colors[i], mood)
  }

  // Generate a color with given hue using golden ratio S/L distribution
  function GenerateColorGolden(h: int, mood: Mood, colorIndex: int, seedS: int, seedL: int): Color
    requires 0 <= h < 360
    requires 0 <= colorIndex < 5
    requires 0 <= seedS <= 100
    requires 0 <= seedL <= 100
  {
    var (s, l) := GoldenSLForMood(mood, colorIndex, seedS, seedL);
    Color(h, s, l)
  }

  // Generate a full 5-color palette using golden ratio S/L distribution
  function GeneratePaletteColors(baseHue: int, mood: Mood, harmony: Harmony, randomSeeds: seq<int>): seq<Color>
    requires ValidBaseHue(baseHue)
    requires ValidRandomSeeds(randomSeeds)
  {
    var hues := AllHarmonyHues(baseHue, harmony);

    if |hues| != 5 then
      // Fallback for Custom harmony: use baseHue for all
      [GenerateColorGolden(baseHue, mood, 0, randomSeeds[0], randomSeeds[1]),
       GenerateColorGolden(baseHue, mood, 1, randomSeeds[2], randomSeeds[3]),
       GenerateColorGolden(baseHue, mood, 2, randomSeeds[4], randomSeeds[5]),
       GenerateColorGolden(baseHue, mood, 3, randomSeeds[6], randomSeeds[7]),
       GenerateColorGolden(baseHue, mood, 4, randomSeeds[8], randomSeeds[9])]
    else
      [GenerateColorGolden(hues[0], mood, 0, randomSeeds[0], randomSeeds[1]),
       GenerateColorGolden(hues[1], mood, 1, randomSeeds[2], randomSeeds[3]),
       GenerateColorGolden(hues[2], mood, 2, randomSeeds[4], randomSeeds[5]),
       GenerateColorGolden(hues[3], mood, 3, randomSeeds[6], randomSeeds[7]),
       GenerateColorGolden(hues[4], mood, 4, randomSeeds[8], randomSeeds[9])]
  }

  // ============================================================================
  // State Transitions (Apply)
  // ============================================================================

  function Apply(m: Model, a: Action): Model
  requires Inv(m)
  {
    match a
    case GeneratePalette(baseHue, mood, harmony, randomSeeds) =>
      if !ValidBaseHue(baseHue) || !ValidRandomSeeds(randomSeeds) then m
      else
        var colors := GeneratePaletteColors(baseHue, mood, harmony, randomSeeds);
        m.(baseHue := baseHue, mood := mood, harmony := harmony, colors := colors,
           adjustmentH := 0, adjustmentS := 0, adjustmentL := 0)

    case AdjustColor(index, deltaH, deltaS, deltaL) =>
      if index < 0 || index >= |m.colors| then m
      else
        ApplyIndependentAdjustment(m, index, deltaH, deltaS, deltaL)

    // AdjustPalette: Applies linked adjustment to all colors
    case AdjustPalette(deltaH, deltaS, deltaL) =>
      var adjusted := ApplyLinkedAdjustment(m, deltaH, deltaS, deltaL);
      adjusted.(adjustmentH := m.adjustmentH + deltaH,
                adjustmentS := m.adjustmentS + deltaS,
                adjustmentL := m.adjustmentL + deltaL)

    case SelectContrastPair(fg, bg) =>
      if 0 <= fg < 5 && 0 <= bg < 5 then
        m.(contrastPair := (fg, bg))
      else m

    case SetColorDirect(index, color) =>
      if index < 0 || index >= |m.colors| then m
      else
        ApplySetColorDirect(m, index, color)

    case RegenerateMood(mood, randomSeeds) =>
      if !ValidRandomSeeds(randomSeeds) then m
      else
        var colors := GeneratePaletteColors(m.baseHue, mood, m.harmony, randomSeeds);
        m.(mood := mood, colors := colors, adjustmentH := 0, adjustmentS := 0, adjustmentL := 0)

    case RegenerateHarmony(harmony, randomSeeds) =>
      if !ValidRandomSeeds(randomSeeds) then m
      else
        var colors := GeneratePaletteColors(m.baseHue, m.mood, harmony, randomSeeds);
        m.(harmony := harmony, colors := colors, adjustmentH := 0, adjustmentS := 0, adjustmentL := 0)

    case RandomizeBaseHue(newBaseHue, randomSeeds) =>
      if !ValidBaseHue(newBaseHue) || !ValidRandomSeeds(randomSeeds) then m
      else
        var colors := GeneratePaletteColors(newBaseHue, m.mood, m.harmony, randomSeeds);
        m.(baseHue := newBaseHue, colors := colors, adjustmentH := 0, adjustmentS := 0, adjustmentL := 0)
  }

  // ============================================================================
  // Linked Adjustment: Shift all colors together
  // ============================================================================

  function ApplyLinkedAdjustment(m: Model, deltaH: int, deltaS: int, deltaL: int): Model
    requires |m.colors| == 5
    requires forall i | 0 <= i < 5 :: ValidColor(m.colors[i])
  {
    // Shift baseHue and regenerate harmony hues
    var newBaseHue := NormalizeHue(m.baseHue + deltaH);
    var newHues := AllHarmonyHues(newBaseHue, m.harmony);

    // Adjust S and L for all colors, preserving hues
    var adjustedColors :=
      if |newHues| == 5 then
        [AdjustColorSL(m.colors[0], newHues[0], deltaS, deltaL),
         AdjustColorSL(m.colors[1], newHues[1], deltaS, deltaL),
         AdjustColorSL(m.colors[2], newHues[2], deltaS, deltaL),
         AdjustColorSL(m.colors[3], newHues[3], deltaS, deltaL),
         AdjustColorSL(m.colors[4], newHues[4], deltaS, deltaL)]
      else (
        // Custom harmony: shift each color's hue by deltaH, adjust S/L
        [AdjustColorSL(m.colors[0], NormalizeHue(m.colors[0].h + deltaH), deltaS, deltaL),
         AdjustColorSL(m.colors[1], NormalizeHue(m.colors[1].h + deltaH), deltaS, deltaL),
         AdjustColorSL(m.colors[2], NormalizeHue(m.colors[2].h + deltaH), deltaS, deltaL),
         AdjustColorSL(m.colors[3], NormalizeHue(m.colors[3].h + deltaH), deltaS, deltaL),
         AdjustColorSL(m.colors[4], NormalizeHue(m.colors[4].h + deltaH), deltaS, deltaL)]
      );

    // Check if any color breaks mood bounds
    var moodBroken := m.mood != Mood.Custom &&
                      exists i | 0 <= i < 5 :: !ColorSatisfiesMood(adjustedColors[i], m.mood);

    var newMood := if moodBroken then Mood.Custom else m.mood;

    m.(baseHue := newBaseHue, colors := adjustedColors, mood := newMood)
  }

  // Helper: Adjust a color's S and L while setting a specific hue
  function AdjustColorSL(c: Color, newHue: int, deltaS: int, deltaL: int): Color
    requires 0 <= newHue < 360
  {
    var newS := Clamp(c.s + deltaS, 0, 100);
    var newL := Clamp(c.l + deltaL, 0, 100);
    Color(newHue, newS, newL)
  }

  // ============================================================================
  // Independent Adjustment: Adjust only one color
  // ============================================================================

  function ApplyIndependentAdjustment(m: Model, index: int, deltaH: int, deltaS: int, deltaL: int): Model
    requires 0 <= index < 5
    requires |m.colors| == 5
  {
    var oldColor := m.colors[index];
    var newColor := ClampColor(Color(
      oldColor.h + deltaH,
      oldColor.s + deltaS,
      oldColor.l + deltaL
    ));

    // Check if hue changed and no longer matches harmony
    var expectedHues := AllHarmonyHues(m.baseHue, m.harmony);
    var hueChanged := |expectedHues| == 5 && newColor.h != expectedHues[index];
    var harmonyBroken := m.harmony != Harmony.Custom && hueChanged;

    // Check if mood bounds broken
    var moodBroken := m.mood != Mood.Custom && !ColorSatisfiesMood(newColor, m.mood);

    var newColors := m.colors[index := newColor];
    var newHarmony := if harmonyBroken then Harmony.Custom else m.harmony;
    var newMood := if moodBroken then Mood.Custom else m.mood;

    m.(colors := newColors, harmony := newHarmony, mood := newMood)
  }

  // ============================================================================
  // SetColorDirect: Try to preserve mood/harmony when possible
  // ============================================================================

  function ApplySetColorDirect(m: Model, index: int, color: Color): Model
    requires 0 <= index < 5
    requires |m.colors| == 5
  {
    var clampedColor := ClampColor(color);

    // Check if new color matches expected harmony hue
    var expectedHues := AllHarmonyHues(m.baseHue, m.harmony);
    var hueMatches := |expectedHues| == 5 && clampedColor.h == expectedHues[index];
    var harmonyPreserved := m.harmony == Harmony.Custom || hueMatches;

    // Check if new color satisfies current mood
    var moodPreserved := m.mood == Mood.Custom || ColorSatisfiesMood(clampedColor, m.mood);

    var newColors := m.colors[index := clampedColor];
    var newHarmony := if harmonyPreserved then m.harmony else Harmony.Custom;
    var newMood := if moodPreserved then m.mood else Mood.Custom;

    m.(colors := newColors, harmony := newHarmony, mood := newMood)
  }

  // ============================================================================
  // Normalize: Ensure invariant holds
  // ============================================================================

  function Normalize(m: Model): Model {
    // Ensure baseHue is in valid range
    var normalizedBaseHue := NormalizeHue(m.baseHue);

    // Ensure all colors are valid (clamped)
    // If we don't have exactly 5 colors, create defaults
    var normalizedColors :=
      if |m.colors| == 5 then [
        ClampColor(m.colors[0]),
        ClampColor(m.colors[1]),
        ClampColor(m.colors[2]),
        ClampColor(m.colors[3]),
        ClampColor(m.colors[4])
      ]
      else [
        Color(0, 0, 0),
        Color(0, 0, 0),
        Color(0, 0, 0),
        Color(0, 0, 0),
        Color(0, 0, 0)
      ];

    // Ensure contrast pair indices are valid
    var normalizedContrastPair :=
      if 0 <= m.contrastPair.0 < 5 && 0 <= m.contrastPair.1 < 5 then
        m.contrastPair
      else
        (0, 1);

    // If mood is not Custom, verify all colors satisfy it; otherwise switch to Custom
    var finalMood :=
      if m.mood == Mood.Custom then Mood.Custom
      else if AllColorsSatisfyMood(normalizedColors, m.mood) then m.mood
      else Mood.Custom;

    // If harmony is not Custom, verify hues match; otherwise switch to Custom
    var finalHarmony :=
      if m.harmony == Harmony.Custom then Harmony.Custom
      else if HuesMatchHarmony(normalizedColors, normalizedBaseHue, m.harmony) then m.harmony
      else Harmony.Custom;

    m.(
      baseHue := normalizedBaseHue,
      colors := normalizedColors,
      contrastPair := normalizedContrastPair,
      mood := finalMood,
      harmony := finalHarmony
    )
  }
}

// === End ColorWheelSpec.dfy ===

module ColorWheelProof {
  import opened CWSpec = ColorWheelSpec

  // Helper lemma: GeneratePaletteColors produces colors satisfying mood
  lemma GeneratePaletteColorsValid(baseHue: int, mood: Mood, harmony: Harmony, randomSeeds: seq<int>)
    requires ValidBaseHue(baseHue)
    requires ValidRandomSeeds(randomSeeds)
    ensures var colors := GeneratePaletteColors(baseHue, mood, harmony, randomSeeds);
            |colors| == 5 &&
            (forall i | 0 <= i < 5 :: ValidColor(colors[i])) &&
            (mood != Mood.Custom ==> forall i | 0 <= i < 5 :: ColorSatisfiesMood(colors[i], mood)) &&
            HuesMatchHarmony(colors, baseHue, harmony)
  {
    var colors := GeneratePaletteColors(baseHue, mood, harmony, randomSeeds);
    var hues := AllHarmonyHues(baseHue, harmony);

    // Prove each color is valid and satisfies mood
    forall i | 0 <= i < 5
      ensures ValidColor(colors[i])
      ensures mood != Mood.Custom ==> ColorSatisfiesMood(colors[i], mood)
    {
      GenerateColorGoldenValid(
        if |hues| == 5 then hues[i] else baseHue,
        mood,
        i,
        randomSeeds[2*i],
        randomSeeds[2*i + 1]
      );
    }

    // Prove hues match harmony
    if harmony != Harmony.Custom && |hues| == 5 {
      assert forall i | 0 <= i < 5 :: colors[i].h == hues[i];
    }
  }

  // Helper lemma: GenerateColorGolden produces a valid color satisfying mood
  lemma GenerateColorGoldenValid(h: int, mood: Mood, colorIndex: int, seedS: int, seedL: int)
    requires 0 <= h < 360
    requires 0 <= colorIndex < 5
    requires 0 <= seedS <= 100
    requires 0 <= seedL <= 100
    ensures ValidColor(GenerateColorGolden(h, mood, colorIndex, seedS, seedL))
    ensures mood != Mood.Custom ==> ColorSatisfiesMood(GenerateColorGolden(h, mood, colorIndex, seedS, seedL), mood)
  {
  }

  // Helper lemma: GoldenSLForMood produces values within mood bounds
  lemma GoldenSLForMoodValid(mood: Mood, colorIndex: int, seedS: int, seedL: int)
    requires 0 <= colorIndex < 5
    requires 0 <= seedS <= 100
    requires 0 <= seedL <= 100
    ensures var (s, l) := GoldenSLForMood(mood, colorIndex, seedS, seedL);
            0 <= s <= 100 && 0 <= l <= 100 &&
            (mood != Mood.Custom ==> ColorSatisfiesMood(Color(0, s, l), mood))
  {
    var (minS, maxS, minL, maxL) := MoodBounds(mood);
    var spreadS := (seedS + colorIndex * GoldenOffset) % 101;
    var spreadL := (seedL + colorIndex * 38) % 101;
    var s := RandomInRange(spreadS, minS, maxS);
    var l := RandomInRange(spreadL, minL, maxL);

    // RandomInRange produces values in [min, max]
    RandomInRangeValid(spreadS, minS, maxS);
    RandomInRangeValid(spreadL, minL, maxL);
  }

  // Helper lemma: RandomInRange produces values in [min, max]
  lemma RandomInRangeValid(seed: int, min: int, max: int)
    requires 0 <= seed <= 100
    requires min <= max
    ensures min <= RandomInRange(seed, min, max) <= max
  {
  }

  // Helper lemma: NormalizeHue produces a valid hue in [0, 360)
  // Compute normalizedColors as done in Normalize
  function NormalizedColors(m: Model): seq<Color> {
    if |m.colors| == 5 then [
      ClampColor(m.colors[0]),
      ClampColor(m.colors[1]),
      ClampColor(m.colors[2]),
      ClampColor(m.colors[3]),
      ClampColor(m.colors[4])
    ]
    else [
      Color(0, 0, 0),
      Color(0, 0, 0),
      Color(0, 0, 0),
      Color(0, 0, 0),
      Color(0, 0, 0)
    ]
  }

  // Key helper: Normalize(m).colors == NormalizedColors(m)
  // Key lemma: if Normalize(m).mood != Custom, then the check on colors passed
  // ============================================================================
  // Behavioral Property: AdjustPalette shifts all hues by deltaH
  // This lemma would have caught the bug where Custom harmony didn't shift hues
  // ============================================================================

  lemma AdjustPaletteShiftsHues(m: Model, deltaH: int, deltaS: int, deltaL: int)
    requires Inv(m)
    ensures var m' := Apply(m, AdjustPalette(deltaH, deltaS, deltaL));
            forall i | 0 <= i < 5 ::
              m'.colors[i].h == NormalizeHue(m.colors[i].h + deltaH)
  {
    var m' := Apply(m, AdjustPalette(deltaH, deltaS, deltaL));
    var newBaseHue := NormalizeHue(m.baseHue + deltaH);
    var newHues := AllHarmonyHues(newBaseHue, m.harmony);

    if |newHues| == 5 {
      // Non-Custom harmony: hues come from harmony pattern
      // The harmony hues are shifted versions of the original harmony hues
      AdjustPaletteShiftsHuesHarmony(m, deltaH, deltaS, deltaL);
    } else {
      // Custom harmony: each hue is shifted individually
      // This is the case that was broken before the fix
      forall i | 0 <= i < 5
        ensures m'.colors[i].h == NormalizeHue(m.colors[i].h + deltaH)
      {
        NormalizeHueValid(m.colors[i].h + deltaH);
      }
    }
  }

  // Helper: For non-Custom harmony, shifted harmony hues equal original hues + deltaH
  lemma AdjustPaletteShiftsHuesHarmony(m: Model, deltaH: int, deltaS: int, deltaL: int)
    requires Inv(m)
    requires |AllHarmonyHues(NormalizeHue(m.baseHue + deltaH), m.harmony)| == 5
    ensures var m' := Apply(m, AdjustPalette(deltaH, deltaS, deltaL));
            forall i | 0 <= i < 5 ::
              m'.colors[i].h == NormalizeHue(m.colors[i].h + deltaH)
  {
    var newBaseHue := NormalizeHue(m.baseHue + deltaH);
    var oldHues := AllHarmonyHues(m.baseHue, m.harmony);
    var newHues := AllHarmonyHues(newBaseHue, m.harmony);

    // Key insight: harmony hues are computed from baseHue
    // So newHues[i] = NormalizeHue(oldHues[i] + deltaH) for each i
    HarmonyHuesShift(m.baseHue, m.harmony, deltaH);

    // Since Inv(m) holds, m.colors[i].h == oldHues[i] (from HuesMatchHarmony)
    assert HuesMatchHarmony(m.colors, m.baseHue, m.harmony);
  }

  // Helper: Shifting baseHue shifts all harmony hues by the same amount
  lemma HarmonyHuesShift(baseHue: int, harmony: Harmony, deltaH: int)
    requires 0 <= baseHue < 360
    requires harmony != Harmony.Custom
    requires |AllHarmonyHues(baseHue, harmony)| == 5
    ensures var oldHues := AllHarmonyHues(baseHue, harmony);
            var newHues := AllHarmonyHues(NormalizeHue(baseHue + deltaH), harmony);
            |newHues| == 5 &&
            forall i | 0 <= i < 5 :: newHues[i] == NormalizeHue(oldHues[i] + deltaH)
  {
    var newBaseHue := NormalizeHue(baseHue + deltaH);
    var oldHues := AllHarmonyHues(baseHue, harmony);
    var newHues := AllHarmonyHues(newBaseHue, harmony);

    // Each harmony type shifts all hues uniformly
    match harmony {
      case Complementary =>
        HarmonyHuesShiftComplementary(baseHue, deltaH);
      case Triadic =>
        HarmonyHuesShiftTriadic(baseHue, deltaH);
      case Analogous =>
        HarmonyHuesShiftAnalogous(baseHue, deltaH);
      case SplitComplement =>
        HarmonyHuesShiftSplitComplement(baseHue, deltaH);
      case Square =>
        HarmonyHuesShiftSquare(baseHue, deltaH);
      case Custom =>
        // Unreachable due to requires
    }
  }

  lemma HarmonyHuesShiftComplementary(baseHue: int, deltaH: int)
    requires 0 <= baseHue < 360
    ensures var oldHues := AllHarmonyHues(baseHue, Complementary);
            var newHues := AllHarmonyHues(NormalizeHue(baseHue + deltaH), Complementary);
            |oldHues| == 5 && |newHues| == 5 &&
            forall i | 0 <= i < 5 :: newHues[i] == NormalizeHue(oldHues[i] + deltaH)
  {
    var newBaseHue := NormalizeHue(baseHue + deltaH);
    NormalizeHueShiftLemma(baseHue, deltaH);
    NormalizeHueShiftLemma(baseHue + 180, deltaH);
    NormalizeHueShiftLemma(baseHue + HueSpread, deltaH);
    NormalizeHueShiftLemma(baseHue + 180 + HueSpread, deltaH);
    NormalizeHueShiftLemma(baseHue - HueSpread, deltaH);
  }

  lemma HarmonyHuesShiftTriadic(baseHue: int, deltaH: int)
    requires 0 <= baseHue < 360
    ensures var oldHues := AllHarmonyHues(baseHue, Triadic);
            var newHues := AllHarmonyHues(NormalizeHue(baseHue + deltaH), Triadic);
            |oldHues| == 5 && |newHues| == 5 &&
            forall i | 0 <= i < 5 :: newHues[i] == NormalizeHue(oldHues[i] + deltaH)
  {
    var newBaseHue := NormalizeHue(baseHue + deltaH);
    NormalizeHueShiftLemma(baseHue, deltaH);
    NormalizeHueShiftLemma(baseHue + 120, deltaH);
    NormalizeHueShiftLemma(baseHue + 240, deltaH);
    NormalizeHueShiftLemma(baseHue + HueSpread, deltaH);
    NormalizeHueShiftLemma(baseHue + 120 - HueSpread, deltaH);
  }

  lemma HarmonyHuesShiftAnalogous(baseHue: int, deltaH: int)
    requires 0 <= baseHue < 360
    ensures var oldHues := AllHarmonyHues(baseHue, Analogous);
            var newHues := AllHarmonyHues(NormalizeHue(baseHue + deltaH), Analogous);
            |oldHues| == 5 && |newHues| == 5 &&
            forall i | 0 <= i < 5 :: newHues[i] == NormalizeHue(oldHues[i] + deltaH)
  {
    var newBaseHue := NormalizeHue(baseHue + deltaH);
    NormalizeHueShiftLemma(baseHue - 30, deltaH);
    NormalizeHueShiftLemma(baseHue - 15, deltaH);
    NormalizeHueShiftLemma(baseHue, deltaH);
    NormalizeHueShiftLemma(baseHue + 15, deltaH);
    NormalizeHueShiftLemma(baseHue + 30, deltaH);
  }

  lemma HarmonyHuesShiftSplitComplement(baseHue: int, deltaH: int)
    requires 0 <= baseHue < 360
    ensures var oldHues := AllHarmonyHues(baseHue, SplitComplement);
            var newHues := AllHarmonyHues(NormalizeHue(baseHue + deltaH), SplitComplement);
            |oldHues| == 5 && |newHues| == 5 &&
            forall i | 0 <= i < 5 :: newHues[i] == NormalizeHue(oldHues[i] + deltaH)
  {
    var newBaseHue := NormalizeHue(baseHue + deltaH);
    NormalizeHueShiftLemma(baseHue, deltaH);
    NormalizeHueShiftLemma(baseHue + 150, deltaH);
    NormalizeHueShiftLemma(baseHue + 210, deltaH);
    NormalizeHueShiftLemma(baseHue + HueSpread, deltaH);
    NormalizeHueShiftLemma(baseHue + 150 - HueSpread, deltaH);
  }

  lemma HarmonyHuesShiftSquare(baseHue: int, deltaH: int)
    requires 0 <= baseHue < 360
    ensures var oldHues := AllHarmonyHues(baseHue, Square);
            var newHues := AllHarmonyHues(NormalizeHue(baseHue + deltaH), Square);
            |oldHues| == 5 && |newHues| == 5 &&
            forall i | 0 <= i < 5 :: newHues[i] == NormalizeHue(oldHues[i] + deltaH)
  {
    var newBaseHue := NormalizeHue(baseHue + deltaH);
    NormalizeHueShiftLemma(baseHue, deltaH);
    NormalizeHueShiftLemma(baseHue + 90, deltaH);
    NormalizeHueShiftLemma(baseHue + 180, deltaH);
    NormalizeHueShiftLemma(baseHue + 270, deltaH);
    NormalizeHueShiftLemma(baseHue + 45, deltaH);
  }

  // Key arithmetic lemma: NormalizeHue(NormalizeHue(a) + b) == NormalizeHue(a + b)
  lemma NormalizeHueShiftLemma(a: int, b: int)
    ensures NormalizeHue(NormalizeHue(a) + b) == NormalizeHue(a + b)
  {
  }

  // Helper: NormalizeHue(x) ≡ x (mod 360)
  }

// === End ColorWheelProof.dfy ===

module ColorWheelDomain refines Domain {
  import opened CWSpec = ColorWheelSpec
  import opened Proof = ColorWheelProof

  type Model = CWSpec.Model
  type Action = CWSpec.Action

  ghost predicate Inv(m: Model) {
    CWSpec.Inv(m)
  }

  function Init(): Model {
    CWSpec.Init()
  }

  function Apply(m: Model, a: Action): Model {
    CWSpec.Apply(m, a)
  }

  function Normalize(m: Model): Model {
    CWSpec.Normalize(m)
  }

  }

module ColorWheelKernel refines Kernel {
  import D = ColorWheelDomain
}

module AppCore {
  import K = ColorWheelKernel
  import D = ColorWheelDomain
  import CWSpec = ColorWheelSpec

  // Initialize with a default palette
  function Init(): K.History {
    K.InitHistory()
  }

  // Action constructors
  function GeneratePalette(baseHue: int, mood: CWSpec.Mood, harmony: CWSpec.Harmony, randomSeeds: seq<int>): D.Action {
    CWSpec.GeneratePalette(baseHue, mood, harmony, randomSeeds)
  }

  function AdjustColor(index: int, deltaH: int, deltaS: int, deltaL: int): D.Action {
    CWSpec.AdjustColor(index, deltaH, deltaS, deltaL)
  }

  // AdjustPalette: Always applies linked adjustment to ALL colors, regardless of mode
  function AdjustPalette(deltaH: int, deltaS: int, deltaL: int): D.Action {
    CWSpec.AdjustPalette(deltaH, deltaS, deltaL)
  }

  function SelectContrastPair(fg: int, bg: int): D.Action {
    CWSpec.SelectContrastPair(fg, bg)
  }

  function SetColorDirect(index: int, color: CWSpec.Color): D.Action {
    CWSpec.SetColorDirect(index, color)
  }

  function RegenerateMood(mood: CWSpec.Mood, randomSeeds: seq<int>): D.Action {
    CWSpec.RegenerateMood(mood, randomSeeds)
  }

  function RegenerateHarmony(harmony: CWSpec.Harmony, randomSeeds: seq<int>): D.Action {
    CWSpec.RegenerateHarmony(harmony, randomSeeds)
  }

  function RandomizeBaseHue(newBaseHue: int, randomSeeds: seq<int>): D.Action {
    CWSpec.RandomizeBaseHue(newBaseHue, randomSeeds)
  }

  // State transitions
  function Dispatch(h: K.History, a: D.Action): K.History requires K.HistInv(h) { K.Do(h, a) }
  function Preview(h: K.History, a: D.Action): K.History requires K.HistInv(h) { K.Preview(h, a) }
  function CommitFrom(h: K.History, baseline: D.Model): K.History { K.CommitFrom(h, baseline) }
  function Undo(h: K.History): K.History { K.Undo(h) }
  function Redo(h: K.History): K.History { K.Redo(h) }

  // Selectors
  function Present(h: K.History): D.Model { h.present }
  function CanUndo(h: K.History): bool { |h.past| > 0 }
  function CanRedo(h: K.History): bool { |h.future| > 0 }
}
