from dataclasses import dataclass, field
from enum import Enum


class Status(str, Enum):
    PASS = "PASS"
    FAIL = "FAIL"
    NOT_PROVEN = "NOT_PROVEN"
    ASSUMED = "ASSUMED"
    INDETERMINATE = "INDETERMINATE"
    NOT_APPLICABLE = "NOT_APPLICABLE"


@dataclass
class Outcome:
    status: Status
    method: str
    evidence: dict = field(default_factory=dict)
    detail: str = ""


@dataclass
class CheckResult:
    check: str
    subject: str
    statement: str
    status: Status
    method: str
    evidence: dict
    detail: str
    conditional_on: list

    @property
    def key(self):
        return "%s:%s" % (self.check, self.subject)

    def to_json(self):
        return {
            "check": self.check,
            "subject": self.subject,
            "statement": self.statement,
            "status": self.status.value,
            "method": self.method,
            "conditional_on": self.conditional_on,
            "detail": self.detail,
            "evidence": self.evidence,
        }
