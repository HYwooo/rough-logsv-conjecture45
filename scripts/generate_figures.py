import math
from pathlib import Path

OUT_PATH = Path(__file__).resolve().parent.parent / "paper" / "figures.typ"


def fmt(v: float) -> str:
    return f"{v:.2f}pt"


def build_fig1_data():
    T = 1.0
    alpha = 0.75
    g = math.gamma(3.0 - alpha)
    W, H_px = 340.0, 145.0
    x_min, x_max = 0.0, 1.0
    y_min, y_max = -0.26, 0.50

    def tx(x: float) -> float:
        return (x - x_min) / (x_max - x_min) * W

    def ty(y: float) -> float:
        return (1.0 - (y - y_min) / (y_max - y_min)) * H_px

    configs = [
        ("2.2", 2.2, "#1f77b4", "rgb(31, 119, 180, 26)"),
        ("3.8", 3.8, "#d95f02", "rgb(217, 95, 2, 30)"),
        ("7.0", 7.0, "#1b9e77", "rgb(27, 158, 119, 36)"),
    ]

    curves_typ = []
    shades_typ = []
    markers_typ = []
    y0 = ty(0.0)

    for _name, A, color, fill_col in configs:
        delta = (2.0 / (A * g)) ** (1.0 / alpha)
        u_cross = T - delta

        # Full curve points clipped softly to avoid huge coordinates outside box
        pts = []
        for i in range(201):
            u = i / 200.0
            c = A * (T - u) ** 2 - 2.0 * ((T - u) ** (2.0 - alpha)) / g
            if c > y_max + 0.35:
                c = y_max + 0.35
            pts.append((tx(u), ty(c)))

        moves = [f"curve.move(({fmt(pts[0][0])}, {fmt(pts[0][1])}))"]
        for px, py in pts[1:]:
            moves.append(f"curve.line(({fmt(px)}, {fmt(py)}))")
        curves_typ.append(
            f'#place(top + left, curve(stroke: 1.35pt + rgb("{color}"), '
            + ", ".join(moves)
            + "))"
        )

        # Negative shading polygon on [u_cross, T]
        neg_pts = [(tx(u_cross), y0)]
        for i in range(1, 81):
            u = u_cross + (T - u_cross) * (i / 80.0)
            c = A * (T - u) ** 2 - 2.0 * ((T - u) ** (2.0 - alpha)) / g
            neg_pts.append((tx(u), ty(min(c, 0.0))))
        neg_pts.append((tx(T), y0))
        smoves = [f"curve.move(({fmt(neg_pts[0][0])}, {fmt(neg_pts[0][1])}))"]
        for px, py in neg_pts[1:]:
            smoves.append(f"curve.line(({fmt(px)}, {fmt(py)}))")
        smoves.append("curve.close()")
        shades_typ.append(
            f"#place(top + left, curve(fill: {fill_col}, stroke: none, "
            + ", ".join(smoves)
            + "))"
        )

        markers_typ.append(
            f'#place(top + left, dx: {fmt(tx(u_cross) - 2.3)}, dy: {fmt(y0 - 2.3)}, '
            f'circle(radius: 2.3pt, fill: rgb("{color}"), stroke: 0.6pt + white))'
        )

    return W, H_px, tx, ty, shades_typ, curves_typ, markers_typ


def build_fig2_data():
    T = 0.01
    sig0 = 0.5
    c1 = -2.0
    q = 0.6
    th = 1.0
    W, H_px = 340.0, 165.0
    lx_min, lx_max = 1.3, 6.0  # log10(M) in [1.3, 6.0] (~20 to 1e6)
    ly_min, ly_max = -7.0, -3.5  # log10(bound) in [1e-7, 3.16e-4]

    def tx(logm: float) -> float:
        return (logm - lx_min) / (lx_max - lx_min) * W

    def ty(logv: float) -> float:
        return (1.0 - (logv - ly_min) / (ly_max - ly_min)) * H_px

    M_table = {0.10: 2.00e2, 0.25: 1.32e3, 0.40: 1.96e4, 0.50: 2.67e5}
    colors = {
        0.10: "#1f77b4",
        0.25: "#d95f02",
        0.40: "#7570b3",
        0.50: "#1b9e77",
    }

    lhs_lines = []
    tail_curves = []
    table_dots = []

    for H in [0.10, 0.25, 0.40, 0.50]:
        col = colors[H]
        alpha = H + 0.5
        g2 = math.gamma(2.5 - H)
        lhs = 2.0 * sig0 * (T ** (2.5 - H)) / math.gamma(3.5 - H)
        y_lhs = ty(math.log10(lhs))

        lhs_lines.append(
            f'#place(top + left, line(start: (0pt, {fmt(y_lhs)}), end: ({fmt(W)}, {fmt(y_lhs)}), '
            f'stroke: (paint: rgb("{col}"), thickness: 0.85pt, dash: "dashed")))'
        )

        # Start curve where delta_M <= T and clip cleanly inside box
        A_min = 2.0 / (g2 * (T ** alpha))
        M_min = max((A_min - c1) / th, 10 ** lx_min)
        l_start = math.log10(M_min)
        pts = []
        for i in range(121):
            lm = l_start + (lx_max - l_start) * (i / 120.0)
            M = 10.0 ** lm
            A = c1 + th * M
            d = (2.0 / (A * g2)) ** (1.0 / alpha)
            tail = (d ** (2.0 - 2.0 * H)) / (q * (1.0 - H) * (g2 ** 2))
            lt = math.log10(tail)
            if lt > ly_max + 0.5:
                lt = ly_max + 0.5
            if lt < ly_min - 0.5:
                lt = ly_min - 0.5
            pts.append((tx(lm), ty(lt)))

        moves = [f"curve.move(({fmt(pts[0][0])}, {fmt(pts[0][1])}))"]
        for px, py in pts[1:]:
            moves.append(f"curve.line(({fmt(px)}, {fmt(py)}))")
        tail_curves.append(
            f'#place(top + left, curve(stroke: 1.4pt + rgb("{col}"), '
            + ", ".join(moves)
            + "))"
        )

        # Table 2 operating point
        Mt = M_table[H]
        At = c1 + th * Mt
        dt = (2.0 / (At * g2)) ** (1.0 / alpha)
        tail_t = (dt ** (2.0 - 2.0 * H)) / (q * (1.0 - H) * (g2 ** 2))
        px_t = tx(math.log10(Mt))
        py_t = ty(math.log10(tail_t))
        table_dots.append(
            f'#place(top + left, dx: {fmt(px_t - 2.8)}, dy: {fmt(py_t - 2.8)}, '
            f'circle(radius: 2.8pt, fill: rgb("{col}"), stroke: 0.7pt + white))'
        )

    return W, H_px, tx, ty, lhs_lines, tail_curves, table_dots


def main():
    W1, H1, tx1, ty1, shades1, curves1, markers1 = build_fig1_data()
    W2, H2, tx2, ty2, lhs2, curves2, dots2 = build_fig2_data()

    # Exact crossover x positions for annotations in Fig 1
    T = 1.0
    alpha = 0.75
    g = math.gamma(2.25)
    u22 = T - (2.0 / (2.2 * g)) ** (1.0 / alpha)
    u38 = T - (2.0 / (3.8 * g)) ** (1.0 / alpha)
    u70 = T - (2.0 / (7.0 * g)) ** (1.0 / alpha)

    typ = f"""// Auto-generated mathematically exact vector figures for RoughLogSV Conjecture 4.5.
// Do not edit curve coordinates manually; regenerate via scripts/generate_figures.py.

#let fig-boundary-layer(lang: "en") = {{
  let is-zh = lang == "zh"
  let legend-item(col, body) = box(baseline: 20%)[
    #line(length: 14pt, stroke: 1.4pt + rgb(col))
    #h(3pt)
    #text(size: 8.5pt)[#body]
  ]

  block(width: 100%)[
    #align(center)[
      #stack(
        dir: ttb,
        spacing: 6pt,
        // Top legend (zero curve overlap)
        box(inset: (bottom: 2pt))[
          #legend-item("#1f77b4")[$A_M = 2.2$]
          #h(12pt)
          #legend-item("#d95f02")[$A_M = 3.8$]
          #h(12pt)
          #legend-item("#1b9e77")[$A_M = 7.0$]
          #h(12pt)
          #text(size: 8pt, fill: luma(90))[
            (#if is-zh [$T = 1, H = 0.25$] else [$T = 1, H = 0.25$])
          ]
        ],
        // Plot frame with outer axis labels
        box(width: {fmt(W1 + 52.0)}, height: {fmt(H1 + 36.0)})[
          // Y-axis label
          #place(top + left, dx: 0pt, dy: {fmt(H1 * 0.43)})[
            #text(size: 8.5pt)[$c_M (u)$]
          ]
          // Y-axis ticks
          #for (val, lbl) in ((-0.2, [$-0.2$]), (0.0, [$0$]), (0.2, [$0.2$]), (0.4, [$0.4$])) {{
            let py = {fmt(H1)} * (1.0 - (val - (-0.26)) / (0.50 - (-0.26)))
            place(top + left, dx: 24pt, dy: py - 4pt)[
              #box(width: 20pt)[#align(right)[#text(size: 7.5pt)[#lbl]]]
            ]
            place(top + left, dx: 46pt, dy: py)[
              #line(length: 3pt, stroke: 0.5pt + black)
            ]
          }}
          // X-axis ticks
          #for u in (0.0, 0.25, 0.50, 0.75, 1.0) {{
            let px = 49pt + {fmt(W1)} * u
            let ulbl = if u == 0.0 [$0$] else if u == 1.0 [$T$] else [$#u T$]
            place(top + left, dx: px, dy: {fmt(H1)} + 0pt)[
              #line(start: (0pt, 0pt), end: (0pt, 3pt), stroke: 0.5pt + black)
            ]
            place(top + left, dx: px - 14pt, dy: {fmt(H1 + 5.0)})[
              #box(width: 28pt)[#align(center)[#text(size: 7.5pt)[#ulbl]]]
            ]
          }}
          // X-axis title
          #place(top + left, dx: 49pt, dy: {fmt(H1 + 20.0)})[
            #box(width: {fmt(W1)})[#align(center)[
              #text(size: 8.5pt)[
                #if is-zh [时间坐标 $u in [0, T]$] else [Time $u in [0, T]$]
              ]
            ]]
          ]
          // Clipped plot canvas
          #place(top + left, dx: 49pt, dy: 0pt)[
            #box(width: {fmt(W1)}, height: {fmt(H1)}, clip: true, stroke: 0.6pt + black)[
              // Zero reference line
              #place(top + left, dy: {fmt(ty1(0.0))})[
                #line(length: {fmt(W1)}, stroke: (paint: luma(120), thickness: 0.6pt, dash: "dotted"))
              ]
              // Vertical guide lines at crossovers
              #place(top + left, dx: {fmt(tx1(u70))}, dy: {fmt(ty1(0.0))})[
                #line(start: (0pt, 0pt), end: (0pt, {fmt(H1 - ty1(0.0))}), stroke: (paint: rgb("#1b9e77"), thickness: 0.5pt, dash: "dotted"))
              ]
              // Shaded negative boundary layers [T - delta_M, T]
              {("\n" + " " * 14).join(shades1)}
              // Curves c_M(u)
              {("\n" + " " * 14).join(curves1)}
              // Crossover dots
              {("\n" + " " * 14).join(markers1)}
              // Non-overlapping annotations inside plot
              #place(top + left, dx: 12pt, dy: 10pt)[
                #text(size: 8pt, fill: luma(40))[
                  #if is-zh [主区间 $c_M (u) >= 0$（可直接舍去）] else [Main interval: $c_M (u) >= 0$]
                ]
              ]
              #place(top + left, dx: {fmt(tx1(u22) - 4.0)}, dy: {fmt(ty1(0.0) - 13.0)})[
                #text(size: 7.5pt, fill: rgb("#1f77b4"))[$T - delta_M$]
              ]
              #place(top + left, dx: {fmt(tx1(u38) - 2.0)}, dy: {fmt(ty1(0.0) - 13.0)})[
                #text(size: 7.5pt, fill: rgb("#d95f02"))[$T - delta_M'$]
              ]
              #place(top + left, dx: {fmt(tx1(u70) - 2.0)}, dy: {fmt(ty1(0.0) - 13.0)})[
                #text(size: 7.5pt, fill: rgb("#1b9e77"))[$T - delta_M''$]
              ]
              #place(top + left, dx: 8pt, dy: {fmt(H1 - 31.0)})[
                #text(size: 7.5pt, fill: luma(50))[
                  #if is-zh [阴影区 $[T - delta_M, T]$\\ 随 $M -> infinity$ 收缩] else [Shaded layer $[T - delta_M, T]$\\ shrinks as $M -> infinity$]
                ]
              ]
            ]
          ]
        ]
      )
    ]
  ]
}}

#let fig-tail-scaling(lang: "en") = {{
  let is-zh = lang == "zh"
  let legend-item(col, body) = box(baseline: 20%)[
    #line(length: 13pt, stroke: 1.4pt + rgb(col))
    #h(3pt)
    #text(size: 8.3pt)[#body]
  ]

  block(width: 100%)[
    #align(center)[
      #stack(
        dir: ttb,
        spacing: 6pt,
        // Top legend
        box(inset: (bottom: 2pt))[
          #legend-item("#1f77b4")[$H = 0.10$]
          #h(10pt)
          #legend-item("#d95f02")[$H = 0.25$]
          #h(10pt)
          #legend-item("#7570b3")[$H = 0.40$]
          #h(10pt)
          #legend-item("#1b9e77")[$H = 0.50$]
          #h(10pt)
          #text(size: 8pt, fill: luma(70))[
            #if is-zh [(虚线：$upright("LHS")_H$；圆点：表 2 参数点)] else [(dashed: $upright("LHS")_H$; dots: Table 2)]
          ]
        ],
        box(width: {fmt(W2 + 58.0)}, height: {fmt(H2 + 36.0)})[
          // Y-axis title (rotated)
          #place(top + left, dx: 2pt, dy: {fmt(H2 * 0.45)})[
            #rotate(-90deg)[
              #text(size: 8pt)[
                #if is-zh [下界各项] else [Bound]
              ]
            ]
          ]
          // Y-axis ticks (log10 in [-7, -3.5])
          #for exp in (-7, -6, -5, -4) {{
            let py = {fmt(H2)} * (1.0 - (exp - (-7.0)) / (-3.5 - (-7.0)))
            place(top + left, dx: 22pt, dy: py - 5pt)[
              #box(width: 28pt)[#align(right)[#text(size: 7.5pt)[$10^(#exp)$]]]
            ]
            place(top + left, dx: 52pt, dy: py)[
              #line(length: 3pt, stroke: 0.5pt + black)
            ]
          }}
          // X-axis ticks (log10(M) in [1.3, 6.0])
          #for exp in (2, 3, 4, 5, 6) {{
            let px = 55pt + {fmt(W2)} * ((exp - 1.3) / (6.0 - 1.3))
            place(top + left, dx: px, dy: {fmt(H2)})[
              #line(start: (0pt, 0pt), end: (0pt, 3pt), stroke: 0.5pt + black)
            ]
            place(top + left, dx: px - 14pt, dy: {fmt(H2 + 5.0)})[
              #box(width: 28pt)[#align(center)[#text(size: 7.5pt)[$10^(#exp)$]]]
            ]
          }}
          // X-axis title
          #place(top + left, dx: 55pt, dy: {fmt(H2 + 20.0)})[
            #box(width: {fmt(W2)})[#align(center)[
              #text(size: 8.5pt)[
                #if is-zh [Cameron--Martin 漂移参数 $M$] else [Cameron--Martin shift $M$]
              ]
            ]]
          ]
          // Clipped plot canvas
          #place(top + left, dx: 55pt, dy: 0pt)[
            #box(width: {fmt(W2)}, height: {fmt(H2)}, clip: true, stroke: 0.6pt + black)[
              // Subtle horizontal log gridlines
              #for exp in (-7, -6, -5, -4) {{
                let py = {fmt(H2)} * (1.0 - (exp - (-7.0)) / (-3.5 - (-7.0)))
                place(top + left, dy: py)[
                  #line(length: {fmt(W2)}, stroke: 0.35pt + luma(228))
                ]
              }}
              // LHS horizontal dashed thresholds
              {("\n" + " " * 14).join(lhs2)}
              // Tail(M) curves
              {("\n" + " " * 14).join(curves2)}
              // Table 2 dots
              {("\n" + " " * 14).join(dots2)}
              // Clean callout in top-right whitespace (above all curves for M >= 2e4)
              #place(top + right, dx: -8pt, dy: 8pt)[
                #box(fill: rgb(255, 255, 255, 220), inset: (x: 4pt, y: 2pt))[
                  #align(right)[
                    #text(size: 7.6pt, fill: luma(55))[
                      #if is-zh [实线低于同色虚线即得 $epsilon.alt_0 > 0$] else [Margin $> 0$ below dashed $upright("LHS")_H$]
                    ]
                  ]
                ]
              ]
            ]
          ]
        ]
      )
    ]
  ]
}}
"""
    OUT_PATH.write_text(typ, encoding="utf-8")
    print(f"Wrote {OUT_PATH} ({len(typ)} bytes)")


if __name__ == "__main__":
    main()
