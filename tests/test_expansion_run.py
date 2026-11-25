"""Unit tests for Gate 1 input loading, protocol amendment policies, trace validation, and checkpoint replay."""

import base64
from copy import deepcopy
from io import BytesIO, StringIO
import json
from types import SimpleNamespace

import pytest

from development.paired_study import expansion_run as run


def line(doc):
    return (run.dump(doc) + "\n").encode()


def encoded(raw):
    return base64.b64encode(raw).decode()


def artifact(raw):
    return {"base64": encoded(raw), "sha256": run.digest(raw)}


def proof(value):
    return artifact(line({"binding_sha256": run.json_pin(value), "rationale": "Synthetic test evidence"}))


@pytest.fixture
def inputs():
    source = b"int main() {}"
    side = {"files": [{"path": "main.cpp", "sha256": run.digest(source)}]}
    pair = {"id": "synthetic", "corpus": "codenet", "cluster_id": "synthetic-cluster", "frame": "Contest",
            "quarantined": False, "slow": side, "fast": side}
    manifest = {"protocol_sha256": run.PROTOCOL_SHA, "status": "scrape_frozen",
                "held_out_used": False, "pairs": [pair]}
    samples = [{"size": size, "stream": stream, "input": str(size), "expected": "1\n"}
               for stream in "abc" for size in (1, 2, 4, 8, 16, 32)]
    variants = {side: {"plain": encoded(source), "counted": encoded(source)} for side in run.SIDES}
    case = {
        "originals": {side: {"path": "main.cpp", "source": encoded(source)} for side in ("slow", "fast")},
        "samples": samples, "variants": variants,
        "evidence": {
            "oracle": proof(["1\n"] * 18),
            "workload": proof([[s["stream"], s["size"], s["input"]] for s in samples]),
            "counter_calibration": proof({side: encoded(source) for side in run.SIDES}),
            "intervention": proof(variants),
        },
    }
    key = "codenet:synthetic"
    bundle = {
        "schema": "eapg.expansion.inputs.v1", "manifest_sha256": run.digest(line(manifest)),
        "desk": {key: {"status": "pass", "evidence": "Synthetic pass"}},
        "desk_evidence": {f"{key}_sha256": run.digest(key.encode()) for key in
                          ("packet", "rater_a", "rater_b", "adjudication")},
        "fixtures": {key: case},
    }
    return manifest, bundle, key


def load(inputs, **kwargs):
    manifest, bundle, _ = inputs
    manifest_raw, bundle_raw = line(manifest), line(bundle)
    return run.load_inputs(BytesIO(manifest_raw + bundle_raw), run.digest(bundle_raw),
                           manifest_pin=run.digest(manifest_raw), **kwargs)


@pytest.fixture
def primary_inputs(inputs):
    _, bundle, _ = inputs
    amendment = artifact(b"Synthetic Amendment 3: primary workflow and sealed batch log")
    held = artifact(line([]))
    bundle["scope_exception"] = {"amendment": amendment, "held": held}
    evidence = bundle["desk_evidence"]
    del evidence["rater_b_sha256"]
    del evidence["adjudication_sha256"]
    evidence["identity_map_sha256"] = run.digest(b"Synthetic identity map")
    evidence["batch_log_sha256"] = run.digest(b"Synthetic sealed batch log")
    return inputs, {"amendment_pin": amendment["sha256"], "held_pin": held["sha256"]}


def test_amendment_3_accepts_primary_only_fixture(primary_inputs, monkeypatch):
    inputs, pins = primary_inputs
    monkeypatch.setattr(run, "AMENDMENT_3_SHA", pins["amendment_pin"])
    header, entries, desk, fixtures = load(inputs, **pins)
    key = inputs[2]
    assert header["s1_design"] == "amendment_3"
    assert header["amendment_sha256"] == pins["amendment_pin"]
    assert set(entries) == set(desk) == set(fixtures) == {key}


@pytest.mark.parametrize("field", ["rater_b_sha256", "agreement_draw_sha256", "author_check",
                                   "author_check_sha256", "author_check_labels"])
@pytest.mark.parametrize("value", [None, "pin"])
def test_amendment_3_rejects_secondary_fields(primary_inputs, monkeypatch, field, value):
    inputs, pins = primary_inputs
    monkeypatch.setattr(run, "AMENDMENT_3_SHA", pins["amendment_pin"])
    inputs[1]["desk_evidence"][field] = run.digest(b"secondary") if value == "pin" else value
    with pytest.raises(ValueError, match="Amendment 3 forbids secondary or author-check S1 evidence"):
        load(inputs, **pins)


@pytest.mark.parametrize("field", ["packet_sha256", "rater_a_sha256", "batch_log_sha256"])
def test_amendment_3_requires_primary_evidence(primary_inputs, monkeypatch, field):
    inputs, pins = primary_inputs
    monkeypatch.setattr(run, "AMENDMENT_3_SHA", pins["amendment_pin"])
    del inputs[1]["desk_evidence"][field]
    with pytest.raises(ValueError, match="missing blind S1 evidence pins"):
        load(inputs, **pins)


def test_amendment_3_constant_is_valid_pin():
    assert run.is_pin(run.AMENDMENT_3_SHA)


def test_amendment_4_constant_is_valid_pin():
    assert run.is_pin(run.AMENDMENT_4_SHA)


@pytest.fixture
def a5_inputs(primary_inputs, monkeypatch):
    inputs, pins = primary_inputs
    manifest, bundle, key = inputs
    monkeypatch.setattr(run, "AMENDMENT_5_SHA", pins["amendment_pin"])
    for suffix in ("stop", "unattempted"):
        row = deepcopy(manifest["pairs"][0])
        row["id"] = suffix
        row["cluster_id"] = suffix
        manifest["pairs"].append(row)
        bundle["desk"][f"codenet:{suffix}"] = deepcopy(bundle["desk"][key])
    bundle["manifest_sha256"] = run.digest(line(manifest))
    bundle["fixture_stops"] = {"codenet:stop": {
        "bucket": "contract", "reason": "insufficient_workload_ladder", "proof": artifact(b"Synthetic SPEC bound")}}
    bundle["not_executed"] = ["codenet:unattempted"]
    return inputs, pins


def test_amendment_5_constant_is_pinned():
    assert run.AMENDMENT_5_SHA == "17de6626bb871cc30f80040bd63f123da8c0b4498231ff63b607045b36fdb469"


def test_amendment_5_valid_partition(a5_inputs):
    inputs, pins = a5_inputs
    header, entries, desk, fixtures = load(inputs, **pins)
    assert header["s1_design"] == "amendment_5"
    assert set(fixtures) == {inputs[2]}
    assert set(fixtures.stops) == {"codenet:stop"}
    assert fixtures.not_executed == {"codenet:unattempted"}
    assert len(entries) == len(desk) == 3
    assert all(judgment["status"] == "pass" for judgment in desk.values())


def test_amendment_5_all_fixtures_with_optional_fields_omitted(primary_inputs, monkeypatch):
    inputs, pins = primary_inputs
    monkeypatch.setattr(run, "AMENDMENT_5_SHA", pins["amendment_pin"])
    _, entries, _, fixtures = load(inputs, **pins)
    assert set(fixtures) == {inputs[2]} and not fixtures.stops and not fixtures.not_executed
    counts = run.summarize(entries, [], pins["amendment_pin"])["by_source"]["CodeNet"]
    assert counts["fixture_stop"] == counts["not_executed"] == counts["desk_stop"] == 0


@pytest.mark.parametrize("group", ["fixtures", "fixture_stops", "not_executed"])
@pytest.mark.parametrize("defect", ["overlap", "missing", "extra"])
def test_amendment_5_rejects_invalid_partition(a5_inputs, group, defect):
    inputs, pins = a5_inputs
    bundle = inputs[1]
    target = bundle[group]
    if defect == "missing":
        target.clear()
    else:
        key = "codenet:extra" if defect == "extra" else (
            "codenet:stop" if group == "fixtures" else inputs[2])
        if group == "not_executed":
            target.append(key)
        else:
            target[key] = deepcopy(next(iter(target.values())))
    with pytest.raises(ValueError, match="partition must exactly cover"):
        load(inputs, **pins)


@pytest.mark.parametrize("bucket,reason", [("contract", "unknown"), ("contract", "original_compile_failure"),
                                           ("unknown", "fixed_contract"), ("route", None)])
def test_amendment_5_rejects_bad_stop_reason(a5_inputs, bucket, reason):
    inputs, pins = a5_inputs
    inputs[1]["fixture_stops"]["codenet:stop"].update(bucket=bucket, reason=reason)
    with pytest.raises(ValueError, match="invalid fixture stop reason"):
        load(inputs, **pins)


@pytest.mark.parametrize("bucket,reason", [(bucket, reason) for bucket, reasons in run.DESK_STOPS.items()
                                          for reason in reasons.split()] + [("route", "original_compile_failure")])
def test_amendment_5_accepts_frozen_stop_reasons(a5_inputs, bucket, reason):
    inputs, pins = a5_inputs
    inputs[1]["fixture_stops"]["codenet:stop"].update(bucket=bucket, reason=reason)
    assert load(inputs, **pins)[3].stops["codenet:stop"]["reason"] == reason


@pytest.mark.parametrize("proof", [artifact(b""), {"base64": encoded(b"proof"), "sha256": "0" * 64},
                                    {"base64": "!", "sha256": "0" * 64}, {}])
def test_amendment_5_rejects_bad_proof(a5_inputs, proof):
    inputs, pins = a5_inputs
    inputs[1]["fixture_stops"]["codenet:stop"]["proof"] = proof
    with pytest.raises(ValueError):
        load(inputs, **pins)


@pytest.mark.parametrize("value", [None, {}, ["codenet:unattempted", "codenet:unattempted"], [{}]])
def test_amendment_5_rejects_invalid_not_executed(a5_inputs, value):
    inputs, pins = a5_inputs
    inputs[1]["not_executed"] = value
    with pytest.raises(ValueError, match="partition"):
        load(inputs, **pins)


@pytest.mark.parametrize("policy", ["amendment_4", "amendment_3", "amendment_1", "adjudicated"])
@pytest.mark.parametrize("field", ["fixture_stops", "not_executed"])
def test_non_a5_pins_reject_partition_fields(primary_inputs, monkeypatch, policy, field):
    inputs, pins = primary_inputs
    bundle = inputs[1]
    if policy in ("amendment_3", "amendment_4"):
        monkeypatch.setattr(run, "AMENDMENT_3_SHA" if policy == "amendment_3" else "AMENDMENT_4_SHA",
                            pins["amendment_pin"])
    else:
        bundle["desk_evidence"]["rater_b_sha256"] = run.digest(b"secondary")
        if policy == "amendment_1":
            bundle["desk_evidence"]["agreement_draw_sha256"] = run.AGREEMENT_DRAW_SHA
        else:
            del bundle["scope_exception"]
            bundle["desk_evidence"]["adjudication_sha256"] = run.digest(b"adjudication")
            pins = {}
    bundle[field] = {} if field == "fixture_stops" else []
    with pytest.raises(ValueError, match="partition requires Amendment 5"):
        load(inputs, **pins)


@pytest.mark.parametrize("field", ["packet_sha256", "rater_a_sha256", "batch_log_sha256"])
def test_amendment_5_requires_primary_pins(a5_inputs, field):
    inputs, pins = a5_inputs
    del inputs[1]["desk_evidence"][field]
    with pytest.raises(ValueError, match="missing blind S1 evidence pins"):
        load(inputs, **pins)


@pytest.mark.parametrize("field", ["rater_b_sha256", "agreement_draw_sha256", "author_check_labels"])
def test_amendment_5_forbids_secondary_fields(a5_inputs, field):
    inputs, pins = a5_inputs
    inputs[1]["desk_evidence"][field] = None
    with pytest.raises(ValueError, match="forbids secondary or author-check"):
        load(inputs, **pins)


def test_amendment_5_allows_indeterminate(a5_inputs):
    inputs, pins = a5_inputs
    inputs[1]["fixtures"].clear()
    inputs[1]["desk"][inputs[2]] = {"status": "indeterminate", "bucket": None, "reason": None,
                                    "evidence": "Synthetic undecidable criteria"}
    _, entries, desk, fixtures = load(inputs, **pins)
    row = run.checkpoint(inputs[2], entries[inputs[2]], desk, fixtures, [])
    assert row["terminal"] == "indeterminate"
    assert run.summarize(entries, [row], pins["amendment_pin"])["by_source"]["CodeNet"]["desk_stop"] == 1


@pytest.mark.parametrize("terminal", ["fixture_stop", "not_executed"])
def test_amendment_5_terminal_replay_and_cli_check(primary_inputs, monkeypatch, tmp_path, capsys, terminal):
    inputs, pins = primary_inputs
    manifest, bundle, key = inputs
    monkeypatch.setattr(run, "AMENDMENT_5_SHA", pins["amendment_pin"])
    bundle["fixtures"].clear()
    if terminal == "fixture_stop":
        bundle["fixture_stops"] = {key: {"bucket": "route", "reason": "original_compile_failure",
                                          "proof": artifact(b"Synthetic Gate 1 stderr")}}
    else:
        bundle["not_executed"] = [key]
    header, entries, desk, fixtures = load(inputs, **pins)
    row = run.checkpoint(key, entries[key], desk, fixtures, [])
    assert row["terminal"] == terminal and row["measurements"] == [] and row["desk"]["status"] == "pass"
    if terminal == "fixture_stop":
        assert (row["bucket"], row["reason"], row["proof_sha256"]) == (
            "route", "original_compile_failure", run.digest(b"Synthetic Gate 1 stderr"))
    receipt = line(header) + line(row)
    assert run.replay(StringIO(receipt.decode()), header, entries, desk, fixtures) == [row]
    assert run.summarize(entries, [row])["by_source"]["CodeNet"][terminal] == 1
    with pytest.raises(ValueError, match="execution record"):
        run.checkpoint(key, entries[key], desk, fixtures, [{}])
    tampered = dict(row, terminal="pass")
    with pytest.raises(ValueError, match="checkpoint order or measurements disagree"):
        run.replay(StringIO((line(header) + line(tampered)).decode()), header, entries, desk, fixtures)
    path = tmp_path / "amendment5.jsonl"
    path.write_bytes(receipt)
    manifest_raw, bundle_raw = line(manifest), line(bundle)
    original = run.load_inputs
    monkeypatch.setattr(run, "load_inputs", lambda stream, pin, **kwargs: original(
        stream, pin, manifest_pin=run.digest(manifest_raw), held_pin=pins["held_pin"], **kwargs))
    monkeypatch.setattr(run.sys, "stdin", SimpleNamespace(buffer=BytesIO(manifest_raw + bundle_raw)))
    monkeypatch.setattr(run.sys, "argv", ["expansion_run", "--bundle-sha256", run.digest(bundle_raw),
                        "--amendment-sha256", pins["amendment_pin"], "--check", str(path)])
    monkeypatch.setattr(run.gate, "invoke", lambda *a, **kw: pytest.fail("Gate 1 must not run"))
    run.main()
    out = capsys.readouterr()
    summary = json.loads(out.out)
    assert not out.err and summary["complete"]
    counts = summary["by_source"]["CodeNet"]
    assert counts[terminal] == counts["drawn"] == counts["processed"] == 1
    assert counts["executed"] == counts["desk_stop"] == counts["compiled"] == counts["fitted"] == 0
    assert counts["fixture_stop"] + counts["not_executed"] == 1


@pytest.fixture
def indeterminate_inputs(primary_inputs, monkeypatch):
    inputs, pins = primary_inputs
    monkeypatch.setattr(run, "AMENDMENT_4_SHA", pins["amendment_pin"])
    inputs[1]["desk"][inputs[2]] = {"status": "indeterminate", "bucket": None, "reason": None,
                                    "evidence": "Synthetic undecidable desk criteria"}
    inputs[1]["fixtures"].clear()
    return inputs, pins


def test_amendment_4_terminal_indeterminate(indeterminate_inputs, monkeypatch):
    inputs, pins = indeterminate_inputs
    monkeypatch.setattr(run, "measure", lambda *a: pytest.fail("indeterminate must not execute"))
    header, entries, desk, fixtures = load(inputs, **pins)
    assert header["s1_design"] == "amendment_4"
    key = inputs[2]
    assert not fixtures and set(entries) == set(desk) == {key}
    row = run.checkpoint(key, entries[key], desk, fixtures, [])
    assert row["terminal"] == "indeterminate" and not row["measurements"]
    assert run.replay(StringIO((line(header) + line(row)).decode()), header, entries, desk, fixtures) == [row]
    summary = run.summarize(entries, [row])
    assert summary["complete"]
    counts = summary["by_source"]["CodeNet"]
    assert counts["drawn"] == counts["processed"] == counts["desk_indeterminate"] == 1
    assert counts["not_desk_rateable"] == 0
    assert counts["compile_attempted"] == counts["run_attempted"] == counts["executed"] == 0


@pytest.mark.parametrize("policy", ["amendment_3", "amendment_1", "adjudicated"])
def test_other_policies_reject_indeterminate(indeterminate_inputs, monkeypatch, policy):
    inputs, pins = indeterminate_inputs
    monkeypatch.setattr(run, "AMENDMENT_4_SHA", run.digest(b"Other A4"))
    if policy == "amendment_3":
        monkeypatch.setattr(run, "AMENDMENT_3_SHA", pins["amendment_pin"])
    else:
        inputs[1]["desk_evidence"]["rater_b_sha256"] = run.digest(b"secondary")
        if policy == "amendment_1":
            inputs[1]["desk_evidence"]["agreement_draw_sha256"] = run.AGREEMENT_DRAW_SHA
        else:
            del inputs[1]["scope_exception"]
            inputs[1]["desk_evidence"]["adjudication_sha256"] = run.digest(b"adjudicated")
            pins = {}
    with pytest.raises(ValueError, match="invalid S1 stop"):
        load(inputs, **pins)


@pytest.mark.parametrize("field,value,message", [("bucket", "route", "S1 indeterminate carries"),
    ("reason", "missing_pinned_dependency", "S1 indeterminate carries"),
    ("evidence", " ", "missing S1 rationale")])
def test_amendment_4_indeterminate_fields(indeterminate_inputs, field, value, message):
    inputs, pins = indeterminate_inputs
    inputs[1]["desk"][inputs[2]][field] = value
    with pytest.raises(ValueError, match=message):
        load(inputs, **pins)


@pytest.mark.parametrize("field", ["packet_sha256", "rater_a_sha256", "batch_log_sha256"])
def test_amendment_4_requires_primary_pins(indeterminate_inputs, field):
    inputs, pins = indeterminate_inputs
    del inputs[1]["desk_evidence"][field]
    with pytest.raises(ValueError, match="missing blind S1 evidence pins"):
        load(inputs, **pins)


@pytest.mark.parametrize("field", ["rater_b_sha256", "agreement_draw_sha256", "author_check", "author_check_labels"])
@pytest.mark.parametrize("value", [None, "pin"])
def test_amendment_4_forbids_secondary_fields(indeterminate_inputs, field, value):
    inputs, pins = indeterminate_inputs
    inputs[1]["desk_evidence"][field] = run.digest(b"secondary") if value == "pin" else value
    with pytest.raises(ValueError, match="forbids secondary or author-check"):
        load(inputs, **pins)


def test_amendment_4_rejects_fixture_for_indeterminate(indeterminate_inputs):
    inputs, pins = indeterminate_inputs
    inputs[1]["fixtures"][inputs[2]] = {}
    with pytest.raises(ValueError, match="need exactly one pinned fixture"):
        load(inputs, **pins)


def test_only_amendment_3_selects_primary_policy(primary_inputs):
    inputs, pins = primary_inputs
    assert run.is_amendment_3(run.AMENDMENT_3_SHA)
    assert not run.is_amendment_3(None)
    assert not run.is_amendment_3("e35995283527e9ea4ae791e2b70ffe310ffe559367e61aa19207e63538f198d3")
    assert not run.is_amendment_3(pins["amendment_pin"])
    with pytest.raises(ValueError, match="missing blind S1 evidence pins"):
        load(inputs, **pins)


@pytest.mark.parametrize("missing", ["rater_b_sha256", "agreement_draw_sha256", "distinctness"])
def test_other_amendment_preserves_agreement_requirements(primary_inputs, monkeypatch, missing):
    inputs, pins = primary_inputs
    monkeypatch.setattr(run, "AMENDMENT_3_SHA", run.digest(b"Different approved amendment"))
    evidence = inputs[1]["desk_evidence"]
    evidence["rater_b_sha256"] = run.digest(b"second rater")
    evidence["agreement_draw_sha256"] = run.AGREEMENT_DRAW_SHA
    if missing == "distinctness":
        evidence["rater_b_sha256"] = evidence["rater_a_sha256"]
    else:
        del evidence[missing]
    message = "missing fixed S1 agreement-draw pin" if missing == "agreement_draw_sha256" else "missing blind S1 evidence pins"
    with pytest.raises(ValueError, match=message):
        load(inputs, **pins)


@pytest.mark.parametrize("policy", ["adjudicated", "amendment_1", "amendment_3"])
def test_s1_design_matches_selected_policy(primary_inputs, monkeypatch, policy):
    inputs, pins = primary_inputs
    monkeypatch.setattr(run, "AMENDMENT_3_SHA", pins["amendment_pin"] if policy == "amendment_3"
                        else run.digest(b"Different approved amendment"))
    if policy != "amendment_3":
        inputs[1]["desk_evidence"]["rater_b_sha256"] = run.digest(b"second rater")
    if policy == "adjudicated":
        del inputs[1]["scope_exception"]
        inputs[1]["desk_evidence"]["adjudication_sha256"] = run.digest(b"adjudication")
        pins = {}
    elif policy == "amendment_1":
        inputs[1]["desk_evidence"]["agreement_draw_sha256"] = run.AGREEMENT_DRAW_SHA
    assert load(inputs, **pins)[0]["s1_design"] == policy


def test_amendment_3_cli_check_replays_checkpoint(primary_inputs, monkeypatch, tmp_path, capsys):
    inputs, pins = primary_inputs
    manifest, bundle, key = inputs
    monkeypatch.setattr(run, "AMENDMENT_3_SHA", pins["amendment_pin"])
    bundle["desk"][key] = {"status": "desk_blocked", "bucket": "route", "reason": "missing_pinned_dependency",
                           "evidence": "Synthetic desk stop"}
    bundle["fixtures"].clear()
    header, entries, desk, fixtures = load(inputs, **pins)
    row = run.checkpoint(key, entries[key], desk, fixtures, [])
    receipt = line(header) + line(row)
    assert run.replay(StringIO(receipt.decode()), header, entries, desk, fixtures) == [row]
    path = tmp_path / "amendment3.jsonl"
    path.write_bytes(receipt)
    manifest_raw, bundle_raw = line(manifest), line(bundle)
    original = run.load_inputs
    monkeypatch.setattr(run, "load_inputs", lambda stream, pin, **kwargs: original(
        stream, pin, manifest_pin=run.digest(manifest_raw), held_pin=pins["held_pin"], **kwargs))
    monkeypatch.setattr(run.sys, "stdin", SimpleNamespace(buffer=BytesIO(manifest_raw + bundle_raw)))
    monkeypatch.setattr(run.sys, "argv", ["expansion_run", "--bundle-sha256", run.digest(bundle_raw),
                        "--amendment-sha256", pins["amendment_pin"], "--check", str(path)])
    monkeypatch.setattr(run.gate, "invoke", lambda *a, **kw: pytest.fail("Gate 1 must not run"))
    run.main()
    out = capsys.readouterr()
    assert not out.err and json.loads(out.out)["complete"] is True


@pytest.mark.parametrize("missing, message", [
    ("bundle", "missing adjudicated S1 labels and case fixtures"),
    ("desk", "incomplete S1 coverage"),
    ("desk_evidence", "missing blind S1 evidence pins"),
    ("fixtures", "need exactly one pinned fixture"),
    ("oracle", "missing independent oracle"),
    ("output", "oracle evidence does not bind"),
    ("workload", "requires six sizes"),
])
def test_cli_refuses_before_gate1(inputs, monkeypatch, capsys, missing, message):
    manifest, bundle, key = inputs
    if missing in ("desk", "desk_evidence", "fixtures"):
        del bundle[missing]
    if missing == "oracle":
        del bundle["fixtures"][key]["evidence"]["oracle"]
    if missing == "output":
        bundle["fixtures"][key]["samples"][0]["expected"] = "changed"
    if missing == "workload":
        bundle["fixtures"][key]["samples"].pop()
    manifest_raw = line(manifest)
    bundle_raw = b"" if missing == "bundle" else line(bundle)
    load_inputs = run.load_inputs
    monkeypatch.setattr(run, "load_inputs", lambda stream, pin, **kwargs: load_inputs(
        stream, pin, manifest_pin=run.digest(manifest_raw), **kwargs))
    monkeypatch.setattr(run.sys, "stdin", SimpleNamespace(buffer=BytesIO(manifest_raw + bundle_raw)))
    monkeypatch.setattr(run.sys, "argv", ["expansion_run", "--bundle-sha256", run.digest(bundle_raw)])
    monkeypatch.setattr(run.gate, "invoke", lambda *a, **kw: pytest.fail("Gate 1 must not run"))
    with pytest.raises(SystemExit) as error:
        run.main()
    assert error.value.code == 2
    out = capsys.readouterr()
    assert not out.out and message in out.err


def test_held_requires_exact_list_and_explicit_amendment(inputs):
    _, bundle, key = inputs
    bundle["desk"].clear()
    bundle["fixtures"].clear()
    held = artifact(line([{"pair_id": "synthetic", "corpus": "codenet",
                           "reason": "unbundled_statement_images"}]))
    amendment = artifact(b"Synthetic amendment")
    bundle["scope_exception"] = {"held": held, "amendment": amendment}
    with pytest.raises(ValueError, match="missing approved S1 amendment"):
        load(inputs)
    with pytest.raises(ValueError, match="wrong S1 amendment"):
        load(inputs, amendment_pin="0" * 64)
    with pytest.raises(ValueError, match="wrong S1 held-list"):
        load(inputs, amendment_pin=amendment["sha256"])
    with pytest.raises(ValueError, match="missing fixed S1 agreement-draw"):
        load(inputs, amendment_pin=amendment["sha256"], held_pin=held["sha256"])
    bundle["desk_evidence"]["agreement_draw_sha256"] = run.AGREEMENT_DRAW_SHA
    del bundle["desk_evidence"]["adjudication_sha256"]
    header, entries, desk, fixtures = load(inputs, amendment_pin=amendment["sha256"], held_pin=held["sha256"])
    row = run.checkpoint(key, entries[key], desk, fixtures, [])
    assert row["terminal"] == run.HELD_LABEL
    assert row["desk"]["reason"] == "unbundled_statement_images"
    assert header["held_list_sha256"] == held["sha256"]
    assert run.summarize(entries, [row])["by_source"]["CodeNet"]["not_desk_rateable"] == 1


def test_cli_check_never_starts_gate1(inputs, monkeypatch, capsys, tmp_path):
    manifest, bundle, key = inputs
    bundle["desk"][key] = {"status": "desk_blocked", "bucket": "route", "reason": "missing_pinned_dependency",
                           "evidence": "Synthetic desk stop"}
    bundle["fixtures"].clear()
    header, entries, desk, fixtures = load(inputs)
    path = tmp_path / "checkpoint.jsonl"
    path.write_bytes(line(header) + line(run.checkpoint(key, entries[key], desk, fixtures, [])))
    manifest_raw, bundle_raw = line(manifest), line(bundle)
    load_inputs = run.load_inputs
    monkeypatch.setattr(run, "load_inputs", lambda stream, pin, **kwargs: load_inputs(
        stream, pin, manifest_pin=run.digest(manifest_raw), **kwargs))
    monkeypatch.setattr(run.sys, "stdin", SimpleNamespace(buffer=BytesIO(manifest_raw + bundle_raw)))
    monkeypatch.setattr(run.sys, "argv", [
        "expansion_run", "--bundle-sha256", run.digest(bundle_raw), "--check", str(path),
    ])
    monkeypatch.setattr(run.gate, "invoke", lambda *a, **kw: pytest.fail("Gate 1 must not run"))
    run.main()
    out = capsys.readouterr()
    assert not out.err
    assert json.loads(out.out)["complete"] is True


def test_cli_resume_replays_stdin_checkpoint_and_continues(inputs, monkeypatch, capsys):
    manifest, bundle, key = inputs
    bundle["desk"][key] = {"status": "desk_blocked", "bucket": "route", "reason": "missing_pinned_dependency",
                           "evidence": "Synthetic desk stop"}
    bundle["fixtures"].clear()
    manifest["pairs"].append({**manifest["pairs"][0], "id": "other", "intake_stop": "intake_unretrievable"})
    manifest_raw = line(manifest)
    bundle["manifest_sha256"] = run.digest(manifest_raw)
    bundle_raw = line(bundle)
    header, entries, desk, fixtures = load(inputs)
    rows = [run.checkpoint(item, entry, desk, fixtures, []) for item, entry in entries.items()]
    load_inputs = run.load_inputs
    monkeypatch.setattr(run, "load_inputs", lambda stream, pin, **kwargs: load_inputs(
        stream, pin, manifest_pin=run.digest(manifest_raw), **kwargs))
    monkeypatch.setattr(run.sys, "stdin", SimpleNamespace(buffer=BytesIO(
        manifest_raw + bundle_raw + line(header) + line(rows[0]))))
    monkeypatch.setattr(run.sys, "argv", ["expansion_run", "--bundle-sha256", run.digest(bundle_raw), "--resume"])
    monkeypatch.setenv("container", "docker")
    monkeypatch.setattr(run.Path, "is_file", lambda path: path.as_posix() == "/.dockerenv")
    monkeypatch.setattr(run.gate, "invoke", lambda command: result(b"15.2.0\n")
                        if command == ["g++", "-dumpfullversion"] else pytest.fail("unexpected sandbox execution"))
    run.main()
    out = capsys.readouterr()
    assert not out.err
    assert [json.loads(record) for record in out.out.splitlines()] == [header, *rows]


def result(stdout=b"", *, rc=0, counter=b"", stderr=b"", timed_out=False):
    return SimpleNamespace(stdout=stdout, returncode=rc, counter_wire=counter,
                           stderr=stderr, timed_out=timed_out, events={})


@pytest.mark.parametrize("rc", [-9, 137, -24, 152])
def test_cpu_limit_observation(rc):
    observed = result(rc=rc)
    observed.events = {"cpu.stat.usage_usec": 8_000_000, "cpu.stat.user_usec": 7_000_000}
    assert run.observation(observed)["caps"] == ["cpu_cap"]


@pytest.mark.parametrize("counter", ["memory.events.oom_kill", "memory.events.oom_group_kill"])
@pytest.mark.parametrize("rc", [-9, 137])
def test_oom_kill_is_memory_not_cpu_limit(counter, rc):
    observed = result(rc=rc)
    observed.events = {counter: 1, "cpu.stat.usage_usec": 9_000_000}
    assert run.observation(observed)["caps"] == ["memory_cap"]


@pytest.mark.parametrize("events,timed_out,caps", [
    ({}, False, []),
    ({"cpu.stat.usage_usec": 7_999_999, "cpu.stat.user_usec": 9_000_000}, False, []),
    ({"cpu.stat.usage_usec": 9_000_000}, True, ["wall_timeout"]),
])
def test_sigkill_without_cpu_limit_evidence(events, timed_out, caps):
    observed = result(rc=137, timed_out=timed_out)
    observed.events = events
    assert run.observation(observed)["caps"] == caps


def test_fully_capped_side_mode_is_insufficient_fit(inputs, monkeypatch):
    _, _, key = inputs
    header, entries, desk, fixtures = load(inputs)
    monkeypatch.setattr(run.gate, "invoke", lambda command, **kwargs: result(
        b"\x7fELF" if command[0] == "/bin/sh" else b""))
    monkeypatch.setattr(run.gate, "execute", lambda binary, data, counter_scale: result(
        b"1\n", counter=b"1 0\n" if counter_scale else b""))
    raw = []
    run.measure(fixtures[key], raw)
    for event in raw:
        if event["step"][0] == "execute" and event["step"][2:] == ["target", "O0"]:
            event.update(status="capped", caps=["cpu_cap"], exit=137, counter=None)
    terminal, details = run.disposition(raw, fixtures[key])
    assert terminal == "insufficient_fit" and not any(details["fits"].values())
    row = run.checkpoint(key, entries[key], desk, fixtures, raw)
    assert run.replay(StringIO((line(header) + line(row)).decode()), header, entries, desk, fixtures) == [row]


@pytest.mark.parametrize("outcome, terminal", [
    ("ok", "no_alert"), ("caps", "insufficient_fit"), ("oracle", "execution_oracle_failure"),
    ("boundary", "support_boundary_closed"), ("infrastructure", "execution_infrastructure_failure"),
    ("counter", None),
])
def test_measure_and_replay(inputs, monkeypatch, outcome, terminal):
    _, _, key = inputs
    header, entries, desk, fixtures = load(inputs)
    case = fixtures[key]

    def invoke(command, **kwargs):
        if outcome == "infrastructure":
            raise RuntimeError("synthetic Gate 1 failure")
        if command[0] == "g++":
            assert "-E" in command
            if outcome == "boundary":
                return result(stderr=b"fatal error: dependency.h: No such file or directory", rc=1)
            return result()
        assert command[:2] == ["/bin/sh", "-ec"]
        return result(b"\x7fELF")

    def execute(binary, data, *, counter_scale):
        assert binary == b"\x7fELF"
        assert counter_scale is None or counter_scale == int(data)
        if outcome == "oracle":
            return result(b"2\n")
        if outcome == "caps" and int(data) >= 8:
            return result(rc=124, timed_out=True)
        if outcome == "counter" and counter_scale:
            return result(b"1\n", counter=b"junk")
        return result(b"1\n", counter=b"1 0\n" if counter_scale else b"")

    monkeypatch.setattr(run.gate, "invoke", invoke)
    monkeypatch.setattr(run.gate, "execute", execute)
    raw = []
    run.measure(case, raw)
    checkpoint = run.checkpoint(key, entries[key], desk, fixtures, raw)
    assert checkpoint["terminal"] == terminal
    receipt = StringIO((line(header) + line(checkpoint)).decode())
    saved = run.replay(receipt, header, entries, desk, fixtures)
    assert saved == [checkpoint]
    counts = run.summarize(entries, saved)["by_source"]["CodeNet"]
    assert counts["fitted"] == (outcome == "ok")
    assert counts["execute_wall_timeout"] == (outcome == "caps")
    assert counts["node_filter_excluded"] == 0
    raw[0]["step"] = ["preprocess", "fast"]
    with pytest.raises(ValueError, match="measurement order"):
        run.replay(StringIO((line(header) + line(checkpoint)).decode()), header, entries, desk, fixtures)
