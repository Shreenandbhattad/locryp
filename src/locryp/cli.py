import argparse
import json
import sys

from . import __version__
from .certificates import CertificateError, Prover, verify_certificate
from .engine import EFFORT, Engine, primality_outcome
from .report import build_report, render_text
from .result import Status
from .spec import SpecError, load_specification, parse_integer

EXIT_OK = 0
EXIT_FAILED = 1
EXIT_USAGE = 2
EXIT_UNSETTLED = 3


def _check(arguments):
    try:
        spec = load_specification(arguments.specification)
        engine = Engine(spec, arguments.effort)
        results = engine.run()
    except (SpecError, OSError) as error:
        print("error: %s" % error, file=sys.stderr)
        return EXIT_USAGE
    if not arguments.quiet:
        print(render_text(spec, results))
    if arguments.report:
        with open(arguments.report, "w", encoding="utf-8") as handle:
            json.dump(build_report(spec, results, arguments.effort), handle, indent=2)
            handle.write("\n")
    statuses = {result.status for result in results}
    if Status.FAIL in statuses:
        return EXIT_FAILED
    if arguments.strict and statuses & {Status.NOT_PROVEN, Status.INDETERMINATE, Status.ASSUMED}:
        return EXIT_UNSETTLED
    return EXIT_OK


def _verify(arguments):
    try:
        with open(arguments.report, encoding="utf-8") as handle:
            report = json.load(handle)
        results = report["results"]
    except (OSError, ValueError, KeyError, TypeError) as error:
        print("error: could not read report: %s" % error, file=sys.stderr)
        return EXIT_USAGE
    checked = 0
    invalid = 0
    for result in results:
        evidence = result.get("evidence") or {}
        certificate = evidence.get("certificate")
        if certificate is None:
            continue
        label = "%s:%s" % (result.get("check"), result.get("subject"))
        checked += 1
        try:
            verify_certificate(certificate, int(evidence["n"]))
            print("VALID    %s  n = %s" % (label, evidence["n"]))
        except (CertificateError, KeyError, ValueError, TypeError) as error:
            invalid += 1
            print("INVALID  %s  %s" % (label, error))
    print("%d certificates checked, %d invalid" % (checked, invalid))
    return EXIT_FAILED if invalid else EXIT_OK


def _prove(arguments):
    try:
        n = parse_integer(arguments.integer, "integer")
    except SpecError as error:
        print("error: %s" % error, file=sys.stderr)
        return EXIT_USAGE
    outcome = primality_outcome(Prover(**EFFORT[arguments.effort]), n)
    print("%s  %s" % (outcome.status.value, outcome.method))
    if outcome.detail:
        print(outcome.detail)
    if "witness" in outcome.evidence:
        print("witness: %s" % json.dumps(outcome.evidence["witness"]))
    if outcome.status == Status.PASS and arguments.output:
        with open(arguments.output, "w", encoding="utf-8") as handle:
            json.dump(outcome.evidence["certificate"], handle, indent=2)
            handle.write("\n")
    if outcome.status == Status.PASS:
        return EXIT_OK
    return EXIT_FAILED if outcome.status == Status.FAIL else EXIT_UNSETTLED


def build_parser():
    parser = argparse.ArgumentParser(
        prog="locryp", description="Proof-carrying consistency checks for the algebra behind cryptographic parameters."
    )
    parser.add_argument("--version", action="version", version="locryp %s" % __version__)
    commands = parser.add_subparsers(dest="command", required=True)

    check = commands.add_parser("check", help="run every applicable check on a specification")
    check.add_argument("specification", help="path to a .json or .toml specification")
    check.add_argument("--report", help="write the JSON evidence report to this path")
    check.add_argument("--effort", choices=sorted(EFFORT), default="normal", help="search budget for certificates")
    check.add_argument("--strict", action="store_true", help="exit with status 3 when any result is not settled")
    check.add_argument("--quiet", action="store_true", help="suppress the text summary")
    check.set_defaults(handler=_check)

    verify = commands.add_parser("verify", help="re-verify every primality certificate in a JSON report")
    verify.add_argument("report", help="path to a report written by locryp check")
    verify.set_defaults(handler=_verify)

    prove = commands.add_parser("prove", help="produce a primality certificate for one integer")
    prove.add_argument("integer", help="decimal or 0x-prefixed hexadecimal integer")
    prove.add_argument("--output", help="write the certificate to this path")
    prove.add_argument("--effort", choices=sorted(EFFORT), default="normal", help="search budget for certificates")
    prove.set_defaults(handler=_prove)
    return parser


def main(argv=None):
    arguments = build_parser().parse_args(argv)
    return arguments.handler(arguments)
