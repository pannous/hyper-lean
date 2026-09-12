#!/usr/bin/env python3
"""Build the exercise and solution papers from notes/counting/algebraic-stochastics-exercises.md.

Each paper is produced in a light and a dark variant, the dark one carrying the
"-dark" name suffix:
  paper/hyperreal-exercises[-dark].tex           problems only, no solutions
  paper/hyperreal-exercise-solutions[-dark].tex  worked solutions
Both omit the theory, which is linked as a separate paper. A light variant of
that theory paper is built here too, from the untouched hyperreals.tex, so that
every cross-link stays inside one colour variant.
"""

import re
import shutil
import subprocess
import sys
from pathlib import Path

PAPER_DIR = Path(__file__).resolve().parent
SOURCE = PAPER_DIR.parent / "notes" / "counting" / "algebraic-stochastics-exercises.md"
SERVER_URL = "https://files.pannous.com"
REPO_URL = "https://github.com/pannous/hyper-lean"
EXERCISES = "hyperreal-exercises"
SOLUTIONS = "hyperreal-exercise-solutions"
THEORY = "hyperreals"

# The theory paper is dark under its plain name, so its light build is the one
# that carries a suffix; the exercise papers are light under their plain name.
THEORY_NAME = {"": THEORY + "-light", "-dark": THEORY}

# Page and link colours; the dark scheme matches the existing theory paper.
COLORS = {
    "": r"\hypersetup{colorlinks=true, linkcolor=blue, citecolor=blue, urlcolor=blue}",
    "-dark": (
        "\\pagecolor{black}\n\\color{white}\n"
        r"\hypersetup{colorlinks=true, linkcolor=cyan, citecolor=cyan, urlcolor=cyan}"
    ),
}


PDFLATEX = shutil.which("pdflatex") or "/Library/TeX/texbin/pdflatex"


def url(name: str) -> str:
    return f"{SERVER_URL}/{name}.pdf"

SECTIONS = ["Problem", "Why this framework", "Solution", "Ingredients and readiness"]

# Spelled-out names inside `backticks` that must become math symbols.
MATH_WORDS = [
    ("R*", r"\Rstar"),
    ("epsilon", r"\eps"),
    ("omega", r"\omega"),
    ("lambda", r"\lambda"),
    ("sigma", r"\sigma"),
    ("theta", r"\theta"),
    ("alpha", r"\alpha"),
    ("delta", r"\delta"),
    ("rho", r"\rho"),
    ("Omega", r"\Omega"),
    ("Phi", r"\Phi"),
    ("phi", r"\phi"),
    (" given ", r"\mid "),
    (" intersect ", r"\cap "),
    (" union ", r"\cup "),
    (" subset ", r"\subset "),
    ("!=", r"\neq "),
    ("<=", r"\le "),
    (">=", r"\ge "),
    ("<<", r"\ll "),
    ("sqrt", r"\sqrt"),
    ("ell", r"\ell"),
    (" in ", r"\in "),
    ("=>", r"\Rightarrow "),
    ("st(", r"\st("),
    ("Var(", r"\Var("),
    ("E[", "E["),
]

LEAN_FILE = re.compile(r"^[\w/.]+\.lean$")


def symbols(text: str) -> str:
    """Replace spelled-out Greek and relation names by their LaTeX symbols."""
    for word, symbol in MATH_WORDS:
        text = text.replace(word, symbol)
    return text


def mathify(code: str) -> str:
    """Turn a `backtick` fragment of the notes into inline math."""
    if code.endswith(".lean"):
        return r"\texttt{%s}" % code.replace("_", r"\_")
    subscripted = re.fullmatch(r"([A-Za-z]{1,4})_([A-Za-z0-9]{1,5})", code)
    if subscripted:
        return "$%s_{%s}$" % (symbols(subscripted[1]), symbols(subscripted[2]))
    if "_" in code and re.fullmatch(r"[A-Za-z0-9_]+", code):
        return r"\texttt{%s}" % code.replace("_", r"\_")
    out = symbols(code)
    out = out.replace("#", r"\#").replace("%", r"\%")
    out = out.replace("*", r"\cdot ")
    # Braces mean sets in the notes and must be escaped, except where they
    # already group an exponent or subscript.
    groups = []
    def protect(match):
        groups.append(match.group(0))
        return "\x00%d\x00" % (len(groups) - 1)
    out = re.sub(r"[\^_]\{[^{}]*\}", protect, out)
    out = out.replace("{", r"\{").replace("}", r"\}")
    out = re.sub(r"\\sqrt\(([^()]*)\)", r"\\sqrt{\1}", out)
    out = re.sub(r"\b([A-Z])(\d+|[ijn])\b", r"\1_{\2}", out)
    out = re.sub(r"\^-(\\?[A-Za-z0-9]+)", r"^{-\1}", out)
    out = re.sub(r"\^([A-Za-z0-9]{2,})", r"^{\1}", out)
    out = re.sub(r"\x00(\d+)\x00", lambda m: groups[int(m[1])], out)
    return "$%s$" % out


# Characters the notes use that pdflatex's default encoding cannot set.
UNICODE = {
    "\u26a0\ufe0f": r"\textbf{Caution:}",
    "\u26a0": r"\textbf{Caution:}",
    "\u2014": "---",
    "\u2013": "--",
    "\u00b7": r"$\cdot$",
    "\u201c": "``",
    "\u201d": "''",
}


def escape_text(text: str) -> str:
    for char in ["&", "%", "#", "_"]:
        text = text.replace(char, "\\" + char)
    for char, replacement in UNICODE.items():
        text = text.replace(char, replacement)
    return text


def convert(text: str) -> str:
    """Convert a markdown paragraph body to LaTeX, preserving \\[ \\] display math."""
    pieces = re.split(r"(\\\[.*?\\\]|`[^`]+`)", text, flags=re.S)
    out = []
    for piece in pieces:
        if piece.startswith("\\["):
            out.append(piece)
        elif piece.startswith("`") and piece.endswith("`"):
            out.append(mathify(piece[1:-1]))
        else:
            piece = escape_text(piece)
            piece = re.sub(r"\*\*(.+?)\*\*", r"\\textbf{\1}", piece, flags=re.S)
            piece = re.sub(r"\*(.+?)\*", r"\\emph{\1}", piece, flags=re.S)
            piece = re.sub(r'"([^"]*)"', r"``\1''", piece)
            out.append(piece)
    return "".join(out)


def render_body(text: str) -> str:
    """Convert a section body, turning numbered markdown lists into enumerate."""
    blocks, current, in_list = [], [], False
    for line in text.split("\n"):
        if re.match(r"^\d+\. ", line):
            if not in_list:
                blocks.append(("text", "\n".join(current)))
                current, in_list = [], True
            current.append(re.sub(r"^\d+\. ", r"\\item ", line))
        elif in_list and (line.startswith("   ") or not line.strip()):
            current.append(line)
        elif in_list:
            blocks.append(("list", "\n".join(current)))
            current, in_list = [line], False
        else:
            current.append(line)
    blocks.append(("list" if in_list else "text", "\n".join(current)))

    rendered = []
    for kind, body in blocks:
        if not body.strip():
            continue
        body = convert(body).strip()
        rendered.append(
            "\\begin{enumerate}[leftmargin=*]\n%s\n\\end{enumerate}" % body
            if kind == "list"
            else body
        )
    return "\n\n".join(rendered)


def parse_exercises(markdown: str):
    exercises = []
    chunks = re.split(r"^## Exercise (\d+) — (.+)$", markdown, flags=re.M)
    for number, title, body in zip(chunks[1::3], chunks[2::3], chunks[3::3]):
        parts = {}
        pattern = r"\*\*(%s)\.\*\*" % "|".join(SECTIONS)
        split = re.split(pattern, body)
        for name, content in zip(split[1::2], split[2::2]):
            parts[name] = content.strip()
        readiness = re.findall(r"\*\*(Now|Partial|Research)[:.,;]?\*\*", parts.get("Ingredients and readiness", ""))
        exercises.append(
            {
                "number": int(number),
                "title": title.strip(),
                "readiness": "/".join(dict.fromkeys(readiness)) or "—",
                **parts,
            }
        )
    return exercises


PREAMBLE = r"""\documentclass[11pt]{article}

\usepackage[margin=1in]{geometry}
\usepackage{amsmath,amssymb,amsthm}
\usepackage{mathtools}
\usepackage{hyperref}
\usepackage{xcolor}
\usepackage{enumitem}

%(colors)s

\newcommand{\R}{\mathbb{R}}
\newcommand{\N}{\mathbb{N}}
\newcommand{\Rstar}{\mathbb{R}^{\star}}
\newcommand{\eps}{\varepsilon}
\let\straightepsilon\epsilon
\renewcommand{\epsilon}{\varepsilon}
\newcommand{\st}{\operatorname{st}}
\newcommand{\Var}{\operatorname{Var}}

\setlist[description]{leftmargin=0pt, style=unboxed, font=\normalfont\bfseries}

\title{%(title)s\\
\large %(subtitle)s}
\author{%(author)s}
\date{\today}

\begin{document}
\maketitle
"""

RULE_COUNTING = r"""
\section*{The one rule you need}

A probability is an ordinary algebraic value in the hyperreal field $\Rstar$,
not a real number obtained by a limit. Fix a positive infinitesimal $\eps$ and
put $\omega = 1/\eps$, so that
\[
  \eps \cdot \omega = 1,
  \qquad 0 < \eps < r \quad\text{for every real } r > 0 .
\]
On a uniform hyperfinite sample space $\Omega$ the probability of an event is a
plain counting ratio,
\[
  P(A) = \frac{\#A}{\#\Omega},
\]
so if the experiment has $A\omega^{n}$ outcomes and the event has $c\omega^{d}$
favorable ones, then
\[
  P(E) = \frac{c\,\omega^{d}}{A\,\omega^{n}} = \frac{c}{A}\,\eps^{\,n-d}.
\]
Everything else is built from these ratios by addition, multiplication,
complement and division. The standard part $\st$ is applied only when the
ordinary real shadow of an answer is explicitly wanted --- which is exactly the
step that classically destroys the information these exercises are about.
"""

RULE_INTEGRAL = r"""
\section*{The two rules you need}

Nothing here is counted, and no hyperfinite sample space is built. The sample
space is an ordinary real interval such as $[0,1]$; all of the hyperreal
content sits in the integral. Fix a positive infinitesimal $\eps$, put
$\omega = 1/\eps$, and take the resolution of the line to be $\eps$: a point
$y$ \emph{is} the half-open dot $[y, y+\eps)$. The integral is then the
hyperfinite left-endpoint Riemann sum with $dx = \eps$,
\[
  \int_{[a,b)} f(x)\,dx
  := \sum_{k=0}^{(b-a)\omega-1} f(a+k\eps)\,\eps ,
\]
evaluated in $\Rstar$ and \emph{not} followed by $\st$. A probability is the
integral of a density, $P(E)=\int_E p$. Because a point is one dot, this
specializes to the identity used on nearly every page:
\[
  \boxed{\;P(\{y\}) = p(y)\,\eps\;}
\]
In particular a uniform law on $[0,1)$ has $p \equiv 1$, so hitting an exact
number has probability $\eps > 0$, not zero --- and $\int_{[0,1)} 1\,dx
= \omega\eps = 1$ exactly, so ordinary interval probabilities are untouched.

An atom of mass $a$ is not a second mechanism bolted onto the density. It is
the density \emph{value} $p(y)=a\omega$, since then $P(\{y\})=a\omega\eps=a$.
The Dirac delta is therefore an ordinary function taking the value $\omega$ on
one dot, and $\st$ is applied only where it is explicitly wanted.
"""

SETUP_TAIL = r"""%(companion)s
\paragraph{Theory.} The axioms, the model, and the underlying calculus are
\emph{not} repeated here. They are developed in the companion paper,
\href{%(theory)s}{\emph{Hyperreal Numbers: $\eps\cdot\omega=1$ --- An
Algebraic, Computable Introduction to Infinitesimal Calculus}}
(\url{%(theory)s}), with the machine-checked Lean~4 development at
\url{%(repo)s}.

\paragraph{Readiness labels.} Each exercise is tagged by what the present
Lean~4 formalization already supports.
\begin{description}
%(labels)s
\end{description}
"""

SOLUTIONS_POINTER = r"""
\section*{Where the solutions are}

Worked solutions are in the companion booklet
\href{%(solutions)s}{\emph{%(title)s --- Solutions}}:
\begin{center}\small\url{%(solutions)s}\end{center}
Try the exercises first: the algebra is short, and the point of each one is
what survives that a real-valued shadow would have deleted.
"""

SOLUTIONS_INTRO_COUNTING = r"""
\paragraph{Exercises.} The problems are stated in full in the companion
booklet \href{%(ex)s}{\emph{Twenty Exercises in Algebraic Probability}}:
\begin{center}\small\url{%(ex)s}\end{center}
Each problem is restated below, so this booklet is self-contained.

\paragraph{Checked Lean solutions.} Every exercise has a checked algebraic
solution kernel:
\begin{itemize}[nosep, leftmargin=2em]
\item exercises 1--7: \texttt{Hyper/AlgebraicStochasticsBasic.lean}
\item exercises 8--14: \texttt{Hyper/AlgebraicStochasticsIntermediate.lean}
\item exercises 15--20: \texttt{Hyper/AlgebraicStochasticsAdvanced.lean}
\end{itemize}
The modules use coefficient-wise algebraic equality and explicitly proved
monomial quotients; their headline theorems have been audited with
\texttt{\#print axioms} and use neither \texttt{sorryAx}, nor the unsafe
raw-list equality axiom, nor unrestricted mixed-order inversion. For a
\textbf{Partial} exercise, a checked kernel means the displayed closed-form
algebra is proved while the reusable event or random-variable abstraction
remains to be built. For a \textbf{Research} exercise, the exact finite algebra
and a proof-carrying interface for the missing analytic or hyperfinite fact are
checked; constructing an instance of that interface is deliberately not passed
off as solved.
"""

CLOSING_COUNTING = r"""
\section*{Suggested framework development order}

The exercises point to a practical implementation sequence: first introduce
events with hyperfinite cardinalities and prove the finite probability laws;
then add finite-valued random variables, finite sums, expectation, variance,
and independence; next make mixed-term division exact or explicitly
leading-order; finally add genuine hyperfinite indices, exponentials,
logarithms, and controlled standard-part theorems. Exercises 1--12 test the
algebraic core, 13--16 drive the statistics API, and 17--20 specify the larger
extensions without pretending that the current representation already proves
them.
"""


SOLUTIONS_INTRO_INTEGRAL = r"""
\paragraph{Exercises.} The problems are stated in full in the companion
booklet \href{%(ex)s}{\emph{Twenty Exercises in Probability on Ordinary
Intervals}}:
\begin{center}\small\url{%(ex)s}\end{center}
Each problem is restated below, so this booklet is self-contained.

\paragraph{No checked kernels yet.} Unlike the counting curriculum, this
framework has \emph{no} Lean~4 formalization: \texttt{Hyper/HyperList.lean}
offers no integral, no density type, and above all no index type of size
$\omega$ to sum over. The solutions below are worked algebra, not machine-checked
theorems, and the readiness labels measure distance from the current code
rather than proofs already obtained. Anything needing a genuine
$\sum_{k<\omega}$ is labelled \textbf{Research} however short its algebra is.
"""

CLOSING_INTEGRAL = r"""
\section*{What to build first}

The exercises fall into three implementation stages. Stage one is a
single-dot integral and the identity $P(\{y\})=p(y)\eps$, which needs nothing
beyond the arithmetic already proved for $\Rstar$. Stage two is an index type
ranging over the $(b-a)\omega$ dots of an interval, with the constant and
power sums; that single addition turns most \textbf{Partial} labels into
\textbf{Now}. Stage three is the analytic layer --- transcendental densities,
$\st$-compatibility with the classical Riemann integral, and conditional laws
on infinitesimal-probability events --- which is where the remaining
\textbf{Research} exercises live.

The conventions used throughout (half-open dots, left endpoints,
$\int\delta = 1$ on one dot, the ambient line $[-\omega,\omega)$) are choices,
not consequences. \texttt{notes/integral/integral-probability-foundations.md}
lists each one together with what the alternative would change; every
alternative changes answers at order $\eps$, which is exactly the order this
framework exists to discuss.
"""

COUNTING = {
    "source": PAPER_DIR.parent / "notes" / "counting" / "algebraic-stochastics-exercises.md",
    "exercises": "hyperreal-exercises",
    "solutions": "hyperreal-exercise-solutions",
    "title": "Twenty Exercises in Algebraic Probability",
    "subtitle": r"The hyperfinite counting model over $\Rstar$",
    "author": "Exercises for engineers, with a machine-checked Lean~4 companion",
    "rule": RULE_COUNTING,
    "labels": r"""\item[Now] reduces to arithmetic and order facts already available for the
concrete $\Rstar$ representation, even if a polished event API is still absent.
\item[Partial] the scalar answer is representable now, but reusable random
variables, hyperfinite counts, or finite-sum infrastructure are missing.
\item[Research] deliberately requires a substantive extension of the framework.""",
    "companion": r"""
\paragraph{The other model.} These exercises count a hyperfinite sample space.
The companion curriculum keeps ordinary real intervals instead and puts the
hyperreal content into the integral, with $dx=\eps$ and $\omega$ as the Dirac
delta; both give $P(\{y\})=\eps$ on the unit interval.
\begin{center}\small\url{%(sibling)s}\end{center}
""",
    "sibling": "hyperreal-integral-exercises",
    "solutions_intro": SOLUTIONS_INTRO_COUNTING,
    "closing": CLOSING_COUNTING,
}

INTEGRAL = {
    "source": PAPER_DIR.parent / "notes" / "integral" / "integral-probability-exercises.md",
    "exercises": "hyperreal-integral-exercises",
    "solutions": "hyperreal-integral-exercise-solutions",
    "title": "Twenty Exercises in Probability on Ordinary Intervals",
    "subtitle": r"Densities, $dx=\eps$, and $\omega$ as the Dirac delta",
    "author": "Exercises for engineers, in the hyperreal field $\\Rstar$",
    "rule": RULE_INTEGRAL,
    "labels": r"""\item[Now] the value and its derivation use only single-dot integrals and
$\Rstar$ arithmetic, which the concrete representation already has.
\item[Partial] the closed form is exact and short, but the derivation sums over
the $(b-a)\omega$ dots of an interval, for which there is no index type yet.
\item[Research] additionally needs transcendental densities, a proved
$\st$-compatibility theorem, or a genuine conditional-law construction.""",
    "companion": r"""
\paragraph{The other model.} These exercises never count anything. The
companion curriculum answers the same questions by counting a hyperfinite
sample space $\{0,\dots,\omega-1\}$ instead, and its solutions are
machine-checked in Lean~4.
\begin{center}\small\url{%(sibling)s}\end{center}
""",
    "sibling": "hyperreal-exercises",
    "solutions_intro": SOLUTIONS_INTRO_INTEGRAL,
    "closing": CLOSING_INTEGRAL,
}

CURRICULA = [COUNTING, INTEGRAL]


def document(header, intro, exercises, body_sections, closing):
    parts = [PREAMBLE % header, intro]
    heading = "Solutions" if "Solution" in body_sections else "Exercises"
    parts.append("\n\\section*{%s}\n" % heading)
    for exercise in exercises:
        parts.append(
            "\n\\subsection*{Exercise %d --- %s \\hfill \\normalfont\\small[%s]}\n"
            % (exercise["number"], convert(exercise["title"]), exercise["readiness"])
        )
        for section in body_sections:
            if section not in exercise:
                continue
            parts.append("\\textbf{%s.} %s\n" % (section, render_body(exercise[section])))
    parts.append(closing)
    parts.append("\n\\end{document}\n")
    return "\n".join(parts)


def compile_tex(name: str, source: str):
    """Write a LaTeX source next to the other papers and run pdflatex twice."""
    tex_path = PAPER_DIR / f"{name}.tex"
    tex_path.write_text(source)
    for _ in range(2):
        result = subprocess.run(
            [PDFLATEX, "-interaction=nonstopmode", "-halt-on-error", tex_path.name],
            cwd=PAPER_DIR,
            capture_output=True,
            text=True,
            errors="replace",
        )
    if result.returncode != 0:
        print(result.stdout[-3000:], file=sys.stderr)
        raise SystemExit(f"pdflatex failed for {name}")
    for suffix in (".aux", ".log", ".out", ".toc"):
        (PAPER_DIR / (name + suffix)).unlink(missing_ok=True)
    print(f"built {PAPER_DIR / (name + '.pdf')}")


def build_theory_light():
    """Re-typeset the untouched dark theory paper in light colours."""
    source = (PAPER_DIR / f"{THEORY}.tex").read_text()
    source = source.replace("\\pagecolor{black}\n", "").replace("\\color{white}\n", "")
    source = source.replace("linkcolor=cyan, citecolor=cyan, urlcolor=cyan",
                            "linkcolor=blue, citecolor=blue, urlcolor=blue")
    compile_tex(THEORY_NAME[""], source)


def build_booklets(curriculum, variant: str):
    """Build both booklets of one curriculum in one colour variant."""
    exercises = parse_exercises(curriculum["source"].read_text())
    assert len(exercises) == 20, f"expected 20 exercises, parsed {len(exercises)}"

    setup = curriculum["rule"] + SETUP_TAIL % {
        "companion": curriculum["companion"] % {"sibling": url(curriculum["sibling"] + variant)},
        "labels": curriculum["labels"],
        "theory": url(THEORY_NAME[variant]),
        "repo": REPO_URL,
    }
    exercises_url = url(curriculum["exercises"] + variant)
    solutions_url = url(curriculum["solutions"] + variant)
    header = {
        "subtitle": curriculum["subtitle"],
        "author": curriculum["author"],
        "colors": COLORS[variant],
    }

    compile_tex(
        curriculum["exercises"] + variant,
        document(
            dict(header, title=curriculum["title"]),
            setup,
            exercises,
            ["Problem", "Why this framework"],
            SOLUTIONS_POINTER % {"solutions": solutions_url, "title": curriculum["title"]},
        ),
    )
    compile_tex(
        curriculum["solutions"] + variant,
        document(
            dict(header, title=curriculum["title"] + ": Solutions"),
            setup + curriculum["solutions_intro"] % {"ex": exercises_url},
            exercises,
            ["Problem", "Solution", "Ingredients and readiness"],
            curriculum["closing"],
        ),
    )


def main():
    build_theory_light()
    for curriculum in CURRICULA:
        for variant in COLORS:
            build_booklets(curriculum, variant)


if __name__ == "__main__":
    main()
