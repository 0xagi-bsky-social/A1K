"""Adversarial local harness tests. Synthetic compilers never certify Lean proofs."""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("replay_v13", HERE / "replay_v13.py")
r = importlib.util.module_from_spec(spec); spec.loader.exec_module(r)


class ReplayTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(); self.root = Path(self.tmp.name)
        (self.root / "SunflowerLean").mkdir(); (self.root / "negative").mkdir(); (self.root / "evidence").mkdir()
        self.metadata = ["lake-manifest.json", "lakefile.toml", "lean-toolchain", "evidence/axiom_audit_inventory.json", "replay.py"]
        for name in self.metadata: (self.root / name).write_text("{}")
        (self.root / "SunflowerLean/A.lean").write_text("import Lean\n")
        (self.root / "SunflowerLean/B.lean").write_text("import SunflowerLean.A\n")
        (self.root / "negative/Bad.lean").write_text("import SunflowerLean.A\nexample : False := by decide\n")
        (self.root / "evidence/axiom_audit_inventory.json").write_text(json.dumps({"modules":[{"roots":["Fixture.checked"]}]}))
        self.fixture = {"path":"negative/Bad.lean", "line_start":2, "line_end":2, "message_pattern":"Tactic `decide` failed: proposition is false"}
        self.refresh_manifest()

    def tearDown(self): self.tmp.cleanup()

    def refresh_manifest(self):
        paths = self.metadata + [p.relative_to(self.root).as_posix() for folder in ["SunflowerLean", "negative"] for p in (self.root / folder).glob("*.lean")]
        self.manifest = {name:r.sha(self.root/name) for name in paths}
        self.write_manifest(self.manifest)

    def write_manifest(self, value):
        (self.root / "source_manifest.json").write_text(json.dumps(value))
        self.manifest_hash = r.sha(self.root / "source_manifest.json")

    def check(self): return r.verify_manifest(self.root, self.manifest_hash, self.metadata)

    def test_exact_manifest_passes(self): self.assertEqual(len(self.check()),8)
    def test_empty_manifest_rejected_even_with_new_digest(self):
        self.write_manifest({})
        with self.assertRaises(r.ReplayError): self.check()
    def test_omitted_module_rejected(self):
        del self.manifest["SunflowerLean/B.lean"]; self.write_manifest(self.manifest)
        with self.assertRaises(r.ReplayError): self.check()
    def test_omitted_harness_rejected(self):
        del self.manifest["replay.py"]; self.write_manifest(self.manifest)
        with self.assertRaises(r.ReplayError): self.check()
    def test_escape_rejected(self):
        self.manifest["../escape"]="0"*64; self.write_manifest(self.manifest)
        with self.assertRaises(r.ReplayError): self.check()
    def test_malformed_digest_rejected(self):
        self.manifest["replay.py"]="x"; self.write_manifest(self.manifest)
        with self.assertRaises(r.ReplayError): self.check()
    def test_manifest_replacement_rejected(self):
        (self.root / "source_manifest.json").write_text("{}")
        with self.assertRaises(r.ReplayError): self.check()
    def test_symlink_source_rejected(self):
        path=self.root/"replay.py"; path.unlink(); path.symlink_to(self.root/"lakefile.toml")
        with self.assertRaises(r.ReplayError): self.check()
    def test_duplicate_json_rejected(self):
        path=self.root/"dupe.json";path.write_text('{"x":1,"x":2}')
        with self.assertRaises(r.ReplayError): r.strict_json(path)
    def test_import_graph_order_and_cycle(self):
        order,_=r.import_order(self.root,self.manifest);self.assertEqual(order,["SunflowerLean.A","SunflowerLean.B"])
        (self.root/"SunflowerLean/A.lean").write_text("import SunflowerLean.B\n")
        with self.assertRaises(r.ReplayError): r.import_order(self.root,self.manifest)
    def error(self, line=2, message="Tactic `decide` failed: proposition is false"):
        return {"severity":"error", "fileName":str(self.root/"negative/Bad.lean"),"pos":{"line":line,"column":1},"data":message}
    def test_target_negative_passes(self): self.assertTrue(r.negative_matches([self.error()],self.fixture,self.root,1))
    def test_error_marker_followed_by_crash_rejected(self):
        for exit_code in [-11, -9, 2, 127]:
            self.assertFalse(r.negative_matches([self.error()],self.fixture,self.root,exit_code))
    def test_unrelated_false_plus_unknown_target_rejected(self):
        self.assertFalse(r.negative_matches([self.error(1), self.error(2,"unknown identifier target")],self.fixture,self.root,1))
    def test_wrong_negative_span_rejected(self): self.assertFalse(r.negative_matches([self.error(1)],self.fixture,self.root,1))
    def test_unrelated_reason_rejected(self): self.assertFalse(r.negative_matches([self.error(2,"unknown identifier target")],self.fixture,self.root,1))
    def test_non_json_diagnostic_rejected(self):
        with self.assertRaises(r.ReplayError): r.diagnostic_records("unstructured failure")
    def test_atomic_exclusive_record_preserves_previous(self):
        path=self.root/"immutable.json";r.atomic_json(path,{"status":"first"},exclusive=True)
        with self.assertRaises(FileExistsError):r.atomic_json(path,{"status":"second"},exclusive=True)
        self.assertEqual(r.strict_json(path),{"status":"first"})
    def make_run(self):
        run=self.root/"run";run.mkdir();(run/"attempts").mkdir();(run/"events").mkdir();return run
    def test_timeout_receipt_and_descendant_cleanup(self):
        run=self.make_run();pidfile=self.root/"child.pid"
        code="import subprocess,time,pathlib; p=subprocess.Popen(['"+sys.executable+"','-c','import time;time.sleep(60)']);pathlib.Path("+repr(str(pidfile))+").write_text(str(p.pid));time.sleep(60)"
        item=r.execute_attempt(run,[sys.executable,"-c",code],self.root,dict(PATH="/usr/bin:/bin"),{"kind":"fixture"},0.3,100000)
        self.assertEqual(item["status"],"timed_out");self.assertGreater(item["wall_seconds"],0.25)
        self.assertGreaterEqual(item["orphaned_descendants_reaped"],1)
        with self.assertRaises(ProcessLookupError):os.kill(int(pidfile.read_text()),0)
        self.assertFalse((run/"completion.json").exists());self.assertIsNotNone(item["peak_rss_kib"])
    def test_interruption_is_receipted(self):
        run=self.make_run()
        item=r.execute_attempt(run,[sys.executable,"-c","import os,signal,time;os.kill(os.getppid(),signal.SIGINT);time.sleep(60)"],self.root,dict(PATH="/usr/bin:/bin"),{"kind":"fixture"},10,100000)
        self.assertEqual(item["status"],"interrupted");self.assertIsNotNone(item["exit_code"])
    def test_release_mutation_detected(self):
        path=self.root/"release.json";path.write_text(json.dumps({"schema":"erdos20-release-commitment/1","files":{"replay.py":r.sha(self.root/"replay.py")}}))
        digest=r.sha(path);self.assertEqual(r.verify_release(self.root,path,digest)["artifact_count"],1)
        (self.root/"replay.py").write_text("changed")
        with self.assertRaises(r.ReplayError):r.verify_release(self.root,path,digest)
    def setup_synthetic_compile(self):
        compiler=self.root/"synthetic-compiler.py"
        compiler.write_text("#!/usr/bin/python3\nimport sys,json,pathlib\nif '--version' in sys.argv: print('SYNTHETIC TEST ONLY');sys.exit()\nsrc=pathlib.Path(sys.argv[-1])\nif 'negative' in src.parts:\n print(json.dumps({'severity':'error','fileName':str(src),'pos':{'line':2,'column':1},'data':'Tactic `decide` failed: proposition is false'}));sys.exit(1)\npathlib.Path(sys.argv[sys.argv.index('-o')+1]).write_bytes(b'SYNTHETIC OBJECT NOT LEAN')\nif src.stem=='A': print(json.dumps({'severity':'information','fileName':str(src),'pos':{'line':1,'column':1},'data':'ERDOS20_AXIOM_AUDIT '+json.dumps({'root':'Fixture.checked','status':'pass','axioms':[]})}))\n")
        compiler.chmod(0o755)
        policy={"schema":r.SCHEMA,"harness_sha256":r.sha(HERE/"replay_v13.py"),"metadata_files":self.metadata,"negative_fixtures":[self.fixture],"lean_options":[]}
        path=self.root/"policy.json";path.write_text(json.dumps(policy))
        self.args=argparse.Namespace(root=self.root,policy=path,expected_policy_sha256=r.sha(path),expected_manifest_sha256=self.manifest_hash,lean=compiler,packages=self.root,runs=self.root/"runs",resume=None,check_only=False,stop_after=None,module_timeout=10.,wall_budget=50.,max_log_bytes=100000)
        return {"environment":{"PATH":"/usr/bin:/bin","LANG":"C.UTF-8"},"synthetic_fixture":True},[]
    def test_unique_runs_checkpoint_resume_and_stale_completion(self):
        environment=self.setup_synthetic_compile()
        with patch.object(r,"verify_environment",return_value=environment):
            self.assertEqual(r.replay(self.args),0)
            first=next(self.args.runs.iterdir());self.assertTrue((first/"completion.json").exists())
            self.args.stop_after=1;self.assertEqual(r.replay(self.args),0)
            second=next(p for p in self.args.runs.iterdir() if p!=first)
            self.assertFalse((second/"completion.json").exists());self.assertTrue((first/"completion.json").exists())
            self.args.resume=second.name;self.args.stop_after=None;self.assertEqual(r.replay(self.args),0)
            self.assertTrue((second/"completion.json").exists())
    def test_resume_full_environment_mutation_rejected(self):
        environment=self.setup_synthetic_compile();self.args.stop_after=1
        with patch.object(r,"verify_environment",return_value=environment):r.replay(self.args)
        self.args.resume=next(self.args.runs.iterdir()).name;self.args.stop_after=None
        changed=({**environment[0],"compiler_changed":True},[])
        with patch.object(r,"verify_environment",return_value=changed):
            with self.assertRaises(r.ReplayError):r.replay(self.args)
    def test_midrun_source_mutation_rejected(self):
        environment=self.setup_synthetic_compile();original=r.execute_attempt
        def mutate(*args,**kwargs):
            result=original(*args,**kwargs)
            (self.root/"SunflowerLean/A.lean").write_text("changed during compiler")
            return result
        with patch.object(r,"verify_environment",return_value=environment),patch.object(r,"execute_attempt",side_effect=mutate):
            with self.assertRaisesRegex(r.ReplayError,"source drift during compiler"):r.replay(self.args)
        self.assertFalse(any(self.args.runs.glob("*/completion.json")))
        status=r.strict_json(next(self.args.runs.glob("*/status.json")))
        self.assertEqual(len(status["receipt_ids"]),1);self.assertGreater(status["charged_attempt_wall_seconds"],0)
    def test_final_dependency_drift_rejected(self):
        environment=self.setup_synthetic_compile();changed=({**environment[0],"cache_changed":True},[])
        with patch.object(r,"verify_environment",side_effect=[environment,changed]):
            with self.assertRaisesRegex(r.ReplayError,"environment drift"):r.replay(self.args)
        self.assertFalse(any(self.args.runs.glob("*/completion.json")))
    def checkpoint(self):
        environment=self.setup_synthetic_compile();self.args.stop_after=1
        with patch.object(r,"verify_environment",return_value=environment):r.replay(self.args)
        run=next(self.args.runs.iterdir());self.args.resume=run.name;self.args.stop_after=None
        return environment,run
    def test_rehashed_forged_source_receipt_rejected(self):
        environment,run=self.checkpoint();status=r.strict_json(run/"status.json");name=status["receipt_ids"][0]
        for suffix in [".started.json",".receipt.json",".validated.json"]:
            path=run/"attempts"/(name+suffix);item=r.strict_json(path);item["identity"]["source_sha256"]="0"*64;r.atomic_json(path,item)
        item=r.strict_json(run/"attempts"/(name+".validated.json"));status["receipts_sha256"]=r.commitment([item]);r.atomic_json(run/"status.json",status)
        with patch.object(r,"verify_environment",return_value=environment):
            with self.assertRaisesRegex(r.ReplayError,"resume source identity"):r.replay(self.args)
    def test_rehashed_forged_command_receipt_rejected(self):
        environment,run=self.checkpoint();status=r.strict_json(run/"status.json");name=status["receipt_ids"][0]
        for suffix in [".started.json",".receipt.json",".validated.json"]:
            path=run/"attempts"/(name+suffix);item=r.strict_json(path);item["command"][0]="/not-the-pinned-compiler";r.atomic_json(path,item)
        item=r.strict_json(run/"attempts"/(name+".validated.json"));status["receipts_sha256"]=r.commitment([item]);r.atomic_json(run/"status.json",status)
        with patch.object(r,"verify_environment",return_value=environment):
            with self.assertRaisesRegex(r.ReplayError,"resume compiler/command"):r.replay(self.args)
    def test_status_context_tampering_rejected(self):
        environment,run=self.checkpoint();status=r.strict_json(run/"status.json");status["context_sha256"]="0"*64;r.atomic_json(run/"status.json",status)
        with patch.object(r,"verify_environment",return_value=environment):
            with self.assertRaisesRegex(r.ReplayError,"status context/run"):r.replay(self.args)
    def test_finalized_attempt_omitted_from_index_rejected(self):
        environment,run=self.checkpoint();r.atomic_json(run/"attempts/unindexed.receipt.json",{})
        with patch.object(r,"verify_environment",return_value=environment):
            with self.assertRaisesRegex(r.ReplayError,"omits or duplicates"):r.replay(self.args)
    def test_altered_compiler_rejected_before_version_execution(self):
        compiler=self.root/"fake";compiler.write_text("claims same version")
        policy={"harness_sha256":r.sha(HERE/"replay_v13.py"),"compiler_sha256":"0"*64}
        with self.assertRaisesRegex(r.ReplayError,"compiler binary identity"):r.verify_environment(self.root,compiler,self.root,policy)

    def setup_dependency_fixture(self):
        packages=self.root/"packages";packages.mkdir();lock=[]
        for name in sorted(r.PACKAGES):
            directory=packages/name;directory.mkdir()
            subprocess.run(["git","init","-q",str(directory)],check=True)
            (directory/"source.txt").write_text(name)
            subprocess.run(["git","add","source.txt"],cwd=directory,check=True)
            subprocess.run(["git","-c","user.name=Fixture","-c","user.email=fixture@example.invalid","commit","-qm","fixture"],cwd=directory,check=True)
            revision=subprocess.check_output(["git","rev-parse","HEAD"],cwd=directory,text=True).strip()
            lock.append({"name":name,"rev":revision})
        (self.root/"lake-manifest.json").write_text(json.dumps({"packages":lock}))
        return packages,lock

    def test_nine_dependency_identity_and_extra_directory(self):
        packages,_=self.setup_dependency_fixture();identities,_=r.dependency_identity(self.root,packages)
        self.assertEqual(len(identities),9);(packages/"shadow").mkdir()
        with self.assertRaisesRegex(r.ReplayError,"extra/missing"):r.dependency_identity(self.root,packages)

    def test_wrong_dependency_revision(self):
        packages,lock=self.setup_dependency_fixture();lock[0]["rev"]="0"*40
        (self.root/"lake-manifest.json").write_text(json.dumps({"packages":lock}))
        with self.assertRaisesRegex(r.ReplayError,"revision mismatch"):r.dependency_identity(self.root,packages)

    def test_dependency_cache_mutation_changes_context(self):
        packages,_=self.setup_dependency_fixture();cache=packages/"mathlib/.lake/build/lib/lean";cache.mkdir(parents=True)
        obj=cache/"Mathlib.olean";obj.write_bytes(b"first")
        first,_=r.dependency_identity(self.root,packages);obj.write_bytes(b"second")
        second,_=r.dependency_identity(self.root,packages);self.assertNotEqual(first,second)

    def test_dependency_project_shadow_rejected(self):
        packages,_=self.setup_dependency_fixture();cache=packages/"mathlib/.lake/build/lib/lean/SunflowerLean";cache.mkdir(parents=True)
        with self.assertRaisesRegex(r.ReplayError,"shadows project"):r.dependency_identity(self.root,packages)


if __name__=="__main__":unittest.main(verbosity=2)
