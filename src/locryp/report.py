import platform

from . import __version__
from .result import Status

ORDER = [status.value for status in Status]


def summarize(results):
    counts = {status: 0 for status in ORDER}
    for result in results:
        counts[result.status.value] += 1
    return counts


def build_report(spec, results, effort):
    return {
        "tool": {"name": "locryp", "version": __version__, "python": platform.python_version()},
        "specification": {"name": spec.name, "sha256": spec.sha256},
        "effort": effort,
        "summary": summarize(results),
        "results": [result.to_json() for result in results],
    }


def render_text(spec, results):
    lines = ["locryp %s, specification %s (sha256 %s)" % (__version__, spec.name, spec.sha256[:16]), ""]
    check_width = max([len(r.check) for r in results] + [5])
    subject_width = max([len(r.subject) for r in results] + [7])
    for result in results:
        lines.append(
            "%-14s %-*s %-*s %s"
            % (result.status.value, check_width, result.check, subject_width, result.subject, result.statement)
        )
        indent = " " * 15
        lines.append("%smethod: %s" % (indent, result.method))
        if result.conditional_on:
            lines.append("%sconditional on: %s" % (indent, ", ".join(result.conditional_on)))
        if result.detail:
            lines.append("%s%s" % (indent, result.detail))
    counts = summarize(results)
    lines.append("")
    lines.append(", ".join("%d %s" % (counts[s], s) for s in ORDER if counts[s]))
    return "\n".join(lines)
