# TerraLink QGIS Plugin 1.8.2

**Ecological corridor planning for habitat connectivity**

TerraLink is a QGIS plugin for building and comparing habitat-corridor scenarios under spatial, budget, and barrier constraints. It supports raster and vector inputs, four optimization modes, optional impassable areas, and a PRE/POST landscape-metrics report for scenario comparison.

### v1.8.2 change note

This maintenance release keeps the existing corridor objectives, scoring, candidate limits, and budget-selection order. It closes an impassable-area edge case in which Landscape Fluidity and later rescue/refill stages could bypass the normal post-buffer obstacle check, adds vector obstacle-rejection diagnostics to run summaries, and makes the explicit vector-routing toggle apply consistently during terminal-path selection. Routing remains available around obstacles when enabled; when no valid route exists, that candidate is left out of the budget rather than being connected through the barrier. It also documents intentional compatibility fallbacks, malformed-candidate skips, and deterministic non-cryptographic sampling for Bandit’s static analysis; no runtime algorithm or output strategy changed.

---


## Table of Contents

1. [What TerraLink Does](#what-terralink-does)
2. [Installation and Access](#installation-and-access)
3. [How The Current Architecture Works](#how-the-current-architecture-works)
4. [Quick Start](#quick-start)
5. [Optimization Modes](#optimization-modes)
6. [Interpretation Guardrails](#interpretation-guardrails)
7. [Input Modes and Parameters](#input-modes-and-parameters)
8. [Outputs](#outputs)
9. [Landscape Metrics Report](#landscape-metrics-report)
10. [Tips and Best Practices](#tips-and-best-practices)
11. [Troubleshooting](#troubleshooting)
12. [Credits and Contact](#credits-and-contact)

---

## What TerraLink Does

TerraLink analyzes an input of wildlife habitat patches and identifies corridors that best match a chosen connectivity objective. It helps users identify which parts of a landscape, when restored into habitat, are likely to have the greatest effect on connectivity.

In practice, you specify:

- the habitat layer
- the optimization mode
- minimum patch size
- corridor width
- search radius
- corridor budget
- optional impassable areas

TerraLink then runs the corridor analysis, adds output layers to QGIS, and writes tables of run summaries and connectivity metrics of the new landscape.

It is designed for scenario testing rather than one-shot “optimal truth.” The intended workflow is to run several plausible settings and compare the mapped outputs and PRE/POST metrics.

---

## Installation and Access

### Requirements

- QGIS 3.22 or newer
- Standard QGIS Python environment with NumPy, GDAL/OGR, and PyQt

### Install From ZIP

1. Download the TerraLink plugin ZIP.
2. In QGIS, open `Plugins` -> `Manage and Install Plugins`.
3. Choose `Install from ZIP`.
4. Select the ZIP and install it.

### Where To Launch It

After installation, TerraLink is available from:

- the toolbar as `Run TerraLink`
- the QGIS plugin menu
- the Processing Toolbox under `SORUS` -> `TerraLink` -> `Open TerraLink`

---

## How The Current Architecture Works

TerraLink has two **input modes**

### Vector input mode

If you start with polygon habitat patches, TerraLink analyzes those polygons directly.

### Raster input mode

If you start with a raster, TerraLink:

1. reads the habitat values you selected
2. builds habitat and optional raster impassable masks
3. polygonizes the habitat mask into a temporary vector layer
4. sends that temporary vector layer, plus any routing masks, into the same corridor-generation backend used by vector runs

Raster impassables remain as a width-aware routing mask during that delegated vector run. The practical result is that raster and vector runs share the same corridor-selection backend, while raster setup still uses raster values, pixel neighborhood, and raster unit conversion.

---

## Quick Start

1. Load a habitat layer into QGIS.
2. Open TerraLink from the toolbar, menu, or Processing Toolbox.
3. Choose `Raster` or `Vector` input mode.
4. Select the input layer.
5. Set the optimization mode.
6. Set minimum patch size, corridor width, budget, and search radius.
7. Add impassable values or layers if needed.
8. Choose an output folder or keep temporary output enabled.
9. Click `Run`.
10. Review the map layers, run summary and landscape-metrics report.

---

## Optimization Modes

TerraLink currently exposes four optimization modes in both raster and vector input modes. The right mode depends on whether you want one dominant backbone, broad gains in connected habitat area, pair-value-driven component joining, or more route options and redundancy.

### Largest Single Network

- Goal: prioritize one dominant connected network.
- Best for: backbone-style consolidation where you want one main habitat system rather than several medium-sized subnetworks. This may be most useful for wildlife that needs large uninterrupted habitat patches, such as wildcats.
- Behavior: TerraLink concentrates the budget spend on the network that most improves the single largest connected system, and after selection it enforces a single largest connected output if disconnected corridor fragments remain.
- Choose this when:
  - you want to build one flagship core network
  - you are planning around one focal population or one priority movement system
  - you care more about the largest connected block than about spreading gains across the landscape
- Example: you have a fragmented reserve complex and want to use limited restoration budget to create the biggest possible continuous network around the main protected area.

### Most Connected Networks A

- Goal: prioritize high-value joins between the patches and subnetworks a corridor connects.
- Best for: landscapes where the value of a corridor should depend on the current patches and networks it joins, not just whether it creates newly counted connected area.
- Behavior: scores a candidate by the combined value of the patches and networks it joins per unit cost. Patches already inside connected subnetworks are still eligible, so this mode can connect a patch more than once when the additional join is valuable enough.
- Choose this when:
  - you want patch-to-patch joins to stay valuable during the run, even if one or both patches get connected by other corridors elsewhere
  - you want a pair-driven strategy without the explicit single-backbone bias of LSN
- Example: you have many scattered patches, but want TerraLink to keep valuing strategic joins involving patches or networks that have already been connected elsewhere. MCN A can therefore favor corridors into already valuable networks when the join value is high relative to corridor cost.

### Most Connected Networks B

- Goal: maximize total habitat area that ends up in connected networks.
- Best for: broad structural connectivity gains where you want more habitat recruited into connected networks.
- Behavior: scores solutions by connected network area first, then uses lower budget, shorter length, and fewer corridors as tie-breakers. It does not try to force everything into one dominant backbone.
- Choose this when:
  - you want the budget to maximize connected habitat area across the landscape
  - creating several useful networks is acceptable
  - you care more about total connected habitat than about forcing one flagship network
- Example: you have many scattered patches and want TerraLink to spend a limited corridor budget on the set of links that places the most habitat into connected networks. MCN B mainly rewards corridors that bring new habitat into connected networks; it usually will not add extra alternate routes inside a network unless they are part of a chain or later budget-fill behavior.

### Landscape Fluidity

- Goal: reduce difficulty traversing the landscape, create alternate routes, and reduce dependence on chokepoints.
- Best for: improving route quality, shortening movement paths, and adding redundancy rather than only increasing connected area.
- Behavior: can retain more than one useful connection pattern when that meaningfully improves landscape fluidity. Unlike MCN and LSN, LF can keep multiple corridors for the same patch pair when those corridors represent distinct useful routes.
- Choose this when:
  - the landscape is already partly connected but movement is brittle or bottlenecked
  - you care about alternate paths, loop creation, or reduced reliance on a single bridge
  - you want to improve movement quality through the network, not just attach more area
- Example: two large habitat blocks are already linked by one narrow route, and you want to test whether adding alternate pathways around that chokepoint would make the overall network more robust.

---

## Interpretation Guardrails

TerraLink outputs are optimization results under the assumptions you supplied. They should be interpreted as decision support, not as a universal statement of how organisms will move in the landscape.

- A selected corridor is the best use of the specified budget under the chosen mode, patch definition, search radius, corridor width, and barrier setup.
- A corridor not being selected does not mean it has no ecological value. It may simply have ranked lower under the current objective or fallen outside the candidate search space.
- Results are sensitive to scale. Search radius, raster resolution, minimum patch size, and barrier detail can all change which corridors are available or worthwhile.
- Results are also sensitive to ecological framing. Different species, movement assumptions, and habitat definitions can legitimately produce different "best" corridors on the same map.
- TerraLink is not a full current-flow solver like Circuitscape or Omniscape. Even Landscape Fluidity uses graph-based resistance and redundancy logic on selected corridor networks, not continuous current flow across every cell.
- Stronger confidence comes from agreement across runs. Corridors that keep appearing across plausible parameter sets are more defensible than corridors that only appear under one narrow setup.

Recommended interpretation workflow:

- Run more than one plausible scenario rather than relying on a single parameter set.
- Compare map outputs and summary metrics together. Sometimes a certain optimization mode will score best on all metrics and on other landscapes each optimization mode will score best on a different metric.
- If the goal is species-specific planning, build separate runs or presets for each focal species instead of treating one generic run as universally applicable.

---

## Input Modes and Parameters

### Raster Input Mode

Raster mode is for land-cover or habitat rasters where one or more raster values define habitat.

### Raster parameters

- `Layer type`: `Raster`
- `Input layer`: raster layer to analyze
- `Raster units`: `Pixels`, `Metric`, or `Imperial`
- `Pixel neighborhood`: 4- or 8-neighbor patch definition
- `Patch values`: one or more habitat values
- `Min patch size`
- `Budget`
- `Corridor width`
- `Search radius`
- `Assign corridor cells`
- optional `Impassable values`
- optional `Allow corridors to pass through bottlenecks`

### Raster units

- `Pixels` keeps patch size, budget, corridor width, and search radius in raster-cell units.
- `Metric` uses hectares for patch size and budget, meters for corridor width, and kilometers for search radius.
- `Imperial` uses acres for patch size and budget, feet for corridor width, and miles for search radius.
- If the raster CRS is not suitable for measured units, use `Pixels` or reproject the raster first.

### Raster barriers

Raster impassables are configured as value lists or ranges. Habitat cells are treated separately from impassables so corridors can meet patch edges. Bottleneck handling controls whether corridors may squeeze through narrow gaps that would otherwise be blocked by the width constraint.

### Vector Input Mode

Vector mode is for polygon habitat patches where each feature represents one patch.

### Vector parameters

- `Layer type`: `Vector`
- `Input layer`: polygon patch layer
- `Vector units`: `Metric` or `Imperial`
- `Min patch size`
- `Budget`
- `Corridor width`
- `Search radius`
- optional impassable polygon layers
- optional navigator `Grid cell size` for routing around impassables

Vector `Metric` units use hectares for patch size and budget, meters for corridor width, and kilometers for search radius. Vector `Imperial` units use acres, feet, and miles.

### Vector requirements

- The input must be a valid polygon layer.
- The run must contain at least two valid patches after filtering.
- Very large patch counts may be rejected for performance reasons.

---

## Outputs

TerraLink always adds outputs to QGIS. When you save to disk, it also writes output files. When `temporary output` is enabled, mapped layers are added as temporary layers and reports are written to temporary files.

### Corridor Outputs

The current saved corridor backend is vector-based.

- Saved runs write a GeoPackage of corridor outputs.
- Vector-style corridor layers are added to QGIS for both raster and vector input modes.
- Saved runs also write a `Contiguous Areas` layer representing dissolved patch-plus-corridor networks.

In other words, **raster input does not currently produce a native corridor raster output**. Raster input is converted to polygon patches and the resulting outputs follow the vector backend.

### Corridor attributes

Vector corridor outputs include corridor-level attributes such as:

- patch identifiers
- corridor area
- corridor length
- connected area
- efficiency
- flags describing cases such as multipatch or isthmus behavior

### Contiguous areas output

Saved and temporary runs also produce a contiguous-network output representing connected patch-plus-corridor systems.

### Reports And Summary Tables

Both raster and vector runs produce:

- a landscape-metrics text report
- a landscape-metrics table layer in QGIS

Vector-backend runs also produce:

- a vector summary CSV
- a QGIS table layer based on that CSV

Because raster input delegates into the vector backend, raster runs also follow this vector-style summary pattern.

### Raster-Only Display Option

The raster dialog still includes `Assign corridor cells` with these choices:

- `Sum area of patches directly connected`
- `Sum area of total network`
- `Efficiency (corridor area / connected patches)`

These settings are still part of the raster parameter surface, but they should not be interpreted as evidence of a separate native raster corridor-output pipeline.

---

## Landscape Metrics Report

Each run writes a PRE/POST landscape-metrics report for comparison across scenarios.

Depending on the run and available methods, the report can include:

- total connected habitat area
- largest connected network (`LCC`)
- Probability of Connectivity (`PC`)
- mean effective resistance

### What each metric is useful for

- **Total connected habitat area** is useful for checking how much habitat has been brought into multi-patch networks. Use it when the main question is whether a scenario connects more habitat overall, even if that habitat is split across several networks. Higher values usually indicate broader structural connectivity gains.
- **Largest connected network (`LCC`)** is useful for checking whether a scenario builds one large connected habitat system. Use it when planning around one priority movement system, one focal population, or species that benefit from a large continuous network. Higher values indicate a larger dominant network.
- **Probability of Connectivity (`PC`)** is useful for comparing functional connectivity among patches while accounting for patch area and distance-decayed movement probability. Use it when large nearby patches should count more than small or distant patches. Higher values indicate stronger expected connectivity across the landscape.
- **Mean effective resistance** is useful for checking how difficult movement remains through the selected network. Use it when the concern is travel difficulty, detours, bottlenecks, or whether corridors create easier routes between habitat patches. Lower values are better.

### How to use these metrics

- Compare scenarios on the same landscape rather than treating any one metric as an absolute truth.
- Interpret structural and functional metrics separately.
- Be careful about scale, raster resolution, and patch definition.
- Use mapped outputs and the metrics report together.

---

## Tips and Best Practices

- Start with a smaller study area or conservative budget to confirm settings before scaling up.
- Keep search radius realistic; very large values increase runtime. In general the radius does not have to larger than your longest potential corridor
- For raster inputs, start with simple habitat values first.
- For vector inputs, fix invalid geometries before running if you suspect topology issues.
- Use temporary output while iterating quickly, then save to disk once you have a scenario worth keeping.
- Compare multiple runs rather than over-interpreting a single result.

---

## Troubleshooting

### No corridors produced

- Increase budget.
- Increase search radius.
- Reduce corridor width.
- Make sure at least two habitat patches remain after filtering.

### Impassables seem wrong

- Raster: confirm the impassable values actually occur in the raster.
- Vector: confirm selected impassable layers are valid polygon layers.
- Vector: reduce navigator grid cell size if thin barriers are being missed.

### Measured units fail in raster mode

- Reproject the raster to a suitable projected CRS, or switch raster units to `Pixels`.

### Runs are slow

- Reduce study area.
- Increase minimum patch size.
- Use a smaller search radius.
- Simplify barriers or disable them temporarily for diagnosis.

### Landscape metrics fail

- TerraLink still attempts to save an error report if the metrics step fails.
- Check the generated report path in the `Log` tab.

---

## Credits and Contact

TerraLink was created by Ben Bishop at SORUS as a practical QGIS tool for habitat-connectivity planning.

Bug reports and feature requests are welcome through the GitHub issue tracker listed in the plugin metadata or by email at `benjamin.bishop@sorusconsultingllc.com`.

Special thanks to Benjamin Yannis and Christopher Pavia for feedback on early versions of TerraLink.
