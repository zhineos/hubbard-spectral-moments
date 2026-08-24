"""Shared visual language for every figure in this project.

One consistent color/typography system across the manuscript, tied to
the paper's three physical concepts:

    CONNECTIVITY  (mu_2, configuration-graph connectivity)  -> blue
    EXCHANGE      (mu_4, same-spin ring-exchange loops)      -> vermillion
    DOUBLON       (finite-U virtual-doublon correction)      -> green
    THEORY/EXACT reference curves                            -> neutral black, dashed

Colors are drawn from the Okabe-Ito colorblind-safe qualitative
palette. Every figure additionally distinguishes data by line style or
marker shape, not color alone, so the figures remain interpretable in
grayscale.
"""
import matplotlib as mpl
import matplotlib.pyplot as plt

# ---- the three concept colors + neutral reference ----
C_CONNECTIVITY = "#0072B2"   # blue
C_EXCHANGE = "#D55E00"       # vermillion
C_DOUBLON = "#009E73"        # green
C_NEUTRAL = "#333333"        # near-black, exact/theory reference
C_ACCENT = "#E69F00"         # orange, rare secondary accent

# sequential families (for ordered parameters like d, U, L) built by
# blending each concept color toward white -- reads correctly in
# grayscale (monotonic darkening) and avoids matplotlib's arbitrary
# default color cycle.
def _shades(hex_color, n, lo=0.4, hi=1.0):
    import numpy as np
    rgb = mpl.colors.to_rgb(hex_color)
    white = (1.0, 1.0, 1.0)
    fracs = np.linspace(hi, lo, n)  # darkest (closest to hex_color) last
    return [mpl.colors.to_hex(tuple(f * c + (1 - f) * w
                                    for c, w in zip(rgb, white)))
            for f in fracs]


def connectivity_shades(n):
    return _shades(C_CONNECTIVITY, n)


def doublon_shades(n):
    return _shades(C_DOUBLON, n)


def exchange_shades(n):
    return _shades(C_EXCHANGE, n)


def concept_cmap(hex_color):
    """Continuous pale-gray -> hex_color colormap, for coloring points
    by a continuous physical variable (e.g. <N_d>) rather than a
    discrete category. Anchored at light gray, not white, so the
    zero-value end stays visible against a white plot background."""
    pale = (0.85, 0.85, 0.85)
    rgb = mpl.colors.to_rgb(hex_color)
    return mpl.colors.LinearSegmentedColormap.from_list(
        "concept", [pale, rgb])


def doublon_cmap():
    return concept_cmap(C_DOUBLON)


# markers: shape encodes a secondary categorical variable (n, sector, ...)
MARKERS = ["o", "s", "^", "D", "v", "P"]
LS_THEORY = "--"
LS_DATA = "-"

FIGWIDTH_SINGLE = 4.6   # inches -> LaTeX \includegraphics[width=0.68\textwidth]
FIGWIDTH_MULTI = 7.2    # inches -> LaTeX \includegraphics[width=0.98\textwidth]
DPI = 300


def apply():
    """Call once at the top of every figure script."""
    mpl.rcParams.update({
        "font.size": 10,
        "font.family": "sans-serif",
        "axes.labelsize": 11,
        "axes.titlesize": 11,
        "axes.titleweight": "bold",
        "xtick.labelsize": 9,
        "ytick.labelsize": 9,
        "legend.fontsize": 8.5,
        "legend.frameon": False,
        "lines.linewidth": 1.4,
        "lines.markersize": 5.5,
        "lines.markeredgewidth": 0.9,
        "axes.linewidth": 0.8,
        "xtick.direction": "in",
        "ytick.direction": "in",
        "xtick.top": True,
        "ytick.right": True,
        "figure.dpi": 120,
        "savefig.dpi": DPI,
        "savefig.bbox": "tight",
    })


def panel_label(ax, letter, loc="upper left", color="black"):
    """Bold (a)/(b)/(c) panel label, consistent placement across figures."""
    x, ha = (0.03, "left") if "left" in loc else (0.97, "right")
    y, va = (0.95, "top") if "upper" in loc else (0.05, "bottom")
    ax.text(x, y, f"({letter})", transform=ax.transAxes, fontsize=11,
             fontweight="bold", ha=ha, va=va, color=color)


def style_axes(ax):
    ax.grid(alpha=0.18, lw=0.6)
