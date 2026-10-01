import argparse
import pathlib
import subprocess
import sys
import os
import shutil
import shlex
import time
import tempfile
from typing import Optional

from src import btorwit2moxiwit, moxiwit2nuxmvwit, log

FILE_NAME = pathlib.Path(__file__).name
FILE_DIR = pathlib.Path(__file__).parent

btormc_path = FILE_DIR / "deps" / "btormc"
avr_path = FILE_DIR / "deps" / "avr"
pono_path = FILE_DIR / "deps" / "pono" 
ric3_path = FILE_DIR / "deps" / "rIC3"
translate_path = FILE_DIR / "translate.py"

# Backend table: model checker -> engine -> command-line flags selecting that
# engine. An engine missing from a backend's entry is rejected by the CLI.
ENGINE_FLAGS = {
    "btormc": {"bmc": [],            "kind": ["--kind"]},
    "avr":    {"bmc": ["--bmc"],     "kind": ["--kind"],    "ic3sa": []},
    "pono":   {"bmc": ["-e", "bmc"], "kind": ["-e", "ind"], "ic3ia": ["-e", "ic3ia"]},
    "ric3":   {"bmc": ["-e", "bmc"], "kind": ["-e", "kind"], "ic3": ["-e", "ic3"]},
}


def run_btormc(btormc_path: pathlib.Path, btor_path: pathlib.Path, timeout: int, kmax: int, engine: str, backend_args: list[str]) -> int:
    log.debug(1, f"Running btormc over {btor_path}", FILE_NAME)
    label = btor_path.stem

    command = [
        str(btormc_path), 
        str(btor_path), 
        "-kmax", str(kmax), 
        "--trace-gen-full",
    ]
    
    command += ENGINE_FLAGS["btormc"][engine] + backend_args

    start_mc = time.perf_counter()

    try:
        proc = subprocess.run(command, capture_output=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        print("timeout")
        return 1
    
    end_mc = time.perf_counter()

    if proc.returncode:
        log.error(proc.stderr.decode("utf-8"), FILE_NAME)
        log.error(f"btormc failure for query '{label}'", FILE_NAME)
        return proc.returncode
    
    log.debug(1, f"Done model checking in {end_mc-start_mc}s", FILE_NAME)

    btor_witness_bytes = proc.stdout

    btor_witness_path = btor_path.with_suffix(".btor2.cex")
    with open(btor_witness_path, "wb") as f:
        f.write(btor_witness_bytes)

    if btor_witness_bytes.startswith(b'sat'):
        print("sat")
        log.debug(1, f"btormc witness created at {btor_witness_path}", FILE_NAME)
    elif btor_witness_bytes.startswith(b'unsat'):
        print("unsat")
    else:
        print("unknown")

    log.debug(1, f"btormc witness created at {btor_witness_path}", FILE_NAME)

    return 0


def run_avr(avr_path: pathlib.Path, btor_path: pathlib.Path, timeout: int, kmax: int, engine: str, backend_args: list[str]) -> int:
    absolute_btor_path = btor_path.absolute()

    log.debug(1, f"Running avr over {absolute_btor_path}", FILE_NAME)
    label = absolute_btor_path.stem

    avr_output_path = absolute_btor_path.parent
    avr_results_path = avr_output_path / "work_test"

    os.chdir(avr_path)

    command = [
        "python3", 
        "avr.py", str(absolute_btor_path), 
        "--witness", 
        "-o", str(avr_output_path),  
        "--kmax", str(kmax), 
        "--timeout", str(timeout + 10)
    ]
    
    command += ENGINE_FLAGS["avr"][engine] + backend_args

    start_mc = time.perf_counter()

    try:
        proc = subprocess.run(command, capture_output=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        print("timeout")
        return 1

    end_mc = time.perf_counter()

    log.debug(1, f"Done model checking in {end_mc-start_mc}s", FILE_NAME)

    stderr = proc.stderr.decode("utf-8")

    # The fork nianzelee/avr reports the verdict as a "Verification result:
    # avr-{h,v,err}" line on stderr. Upstream AVR does not print that line, so
    # the verdict is then read from result.pr, which holds the finer-grained code.
    result_str = ""
    for line in reversed(stderr.splitlines()):
        if line.startswith("Verification result: "):
            result_str = line[len("Verification result: "):].strip()
            break
    if not result_str:
        try:
            with open(str(avr_results_path / "result.pr"), "r") as f:
                result_str = f.read().strip()
        except OSError:
            pass

    btor_witness_path = absolute_btor_path.with_suffix(".btor2.cex")
    os.chdir("..")

    if result_str == "avr-v":
        print("sat")
        avr_witness_path = [c for c in avr_results_path.glob("cex.witness")]
        avr_witness_path[0].rename(str(btor_witness_path))
    elif result_str in ("avr-h", "avr-h_triv"):
        print("unsat")
        avr_proof_path = [c for c in avr_results_path.glob("inv.txt")]
        if len(avr_proof_path) > 0:
            avr_proof_path[0].rename(str(btor_witness_path.parent / "inv.txt"))
        with open(str(btor_witness_path), "w") as f:
            f.write("unsat")
    elif result_str in ("avr-f_to", "avr-f_to_q"):
        print("timeout")
        btor_witness_path.touch()
        return 1
    elif engine in ("bmc", "kind") and f"safe till step {kmax})" in stderr:
        # Heuristic, verified against upstream AVR (hwmcc25, commit b760f28)
        # and the fork nianzelee/avr (commit 82af52ef): AVR writes
        # the same "avr-err" (result.pr: "avr-f_err") both for a real failure
        # and for BMC or k-induction stopping at --kmax without a verdict, so
        # the verdict alone cannot separate "unknown" from a tool error. The
        # only distinguishing signal is the progress line "(bmc: safe till
        # step K)" / "(kind: safe till step K)" that AVR prints on stderr just
        # before the verdict. Only a run that reached exactly kmax is reported
        # as unknown; every other avr-err is a crash.
        print("unknown")
        btor_witness_path.touch()
    else:
        log.error(stderr, FILE_NAME)
        log.error(f"AVR failure for query '{label}' ({result_str or 'no verdict'})", FILE_NAME)
        print("crash")
        btor_witness_path.touch()
        return 1

    log.debug(1, f"AVR witness created at {btor_witness_path}", FILE_NAME)

    return 0


def run_pono(pono_path: pathlib.Path, btor_path: pathlib.Path, timeout: int, kmax: int, engine: str, backend_args: list[str]) -> int:
    log.debug(1, f"Running pono over {btor_path}", FILE_NAME)
    # label = btor_path.stem

    # Pono 2.0.0 prints the BTOR2 witness only with --witness.
    command = [str(pono_path), "-k", str(kmax), "--witness"]
    command += ENGINE_FLAGS["pono"][engine] + backend_args
    command.append(str(btor_path))

    start_mc = time.perf_counter()

    try:
        proc = subprocess.run(command, capture_output=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        print("timeout")
        return 1

    end_mc = time.perf_counter()

    log.debug(1, f"Done model checking in {end_mc-start_mc}s", FILE_NAME)

    btor_witness_bytes = proc.stdout
    btor_witness_path = btor_path.with_suffix(".btor2.cex")

    if btor_witness_bytes.startswith(b'sat'):
        print("sat")
        with open(btor_witness_path, "wb") as f:
            f.write(btor_witness_bytes)
    elif btor_witness_bytes.startswith(b'unsat'):
        print("unsat")
        with open(btor_witness_path, "wb") as f:
            f.write(btor_witness_bytes)
    elif btor_witness_bytes.startswith(b'unknown'):
        print("unknown")
        btor_witness_path.touch()
    else:
        log.error(proc.stderr.decode("utf-8"), FILE_NAME)
        log.error(f"pono failure for query '{btor_path.stem}'", FILE_NAME)
        print("crash")
        btor_witness_path.touch()
        return 1

    return 0


def run_ric3(ric3_path: pathlib.Path, btor_path: pathlib.Path, timeout: int, kmax: int, engine: str, backend_args: list[str]) -> int:
    log.debug(1, f"Running rIC3 over {btor_path}", FILE_NAME)

    # rIC3 defaults to a 16-thread portfolio, so the engine is always explicit.
    command = [str(ric3_path), "--witness", "--end", str(kmax)]
    command += ENGINE_FLAGS["ric3"][engine] + backend_args
    command.append(str(btor_path))

    start_mc = time.perf_counter()

    try:
        proc = subprocess.run(command, capture_output=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        print("timeout")
        return 1

    end_mc = time.perf_counter()

    log.debug(1, f"Done model checking in {end_mc-start_mc}s", FILE_NAME)

    # rIC3 1.5.2: first stdout line is SAT (exit 10), UNSAT (exit 20) or
    # UNKNOWN (exit 30, bound reached); with --witness the BTOR2 witness
    # (lowercase "sat" header) follows the SAT line.
    verdict, _, btor_witness_bytes = proc.stdout.partition(b"\n")
    btor_witness_path = btor_path.with_suffix(".btor2.cex")

    if verdict == b"SAT" and proc.returncode == 10:
        print("sat")
        with open(btor_witness_path, "wb") as f:
            # rIC3 ends the witness with a blank line after ".", which the
            # BTOR2 witness parser rejects.
            f.write(btor_witness_bytes.rstrip() + b"\n")
    elif verdict == b"UNSAT" and proc.returncode == 20:
        print("unsat")
        with open(btor_witness_path, "wb") as f:
            f.write(b"unsat")
    elif verdict == b"UNKNOWN" and proc.returncode == 30:
        print("unknown")
        btor_witness_path.touch()
    else:
        log.error(proc.stderr.decode("utf-8"), FILE_NAME)
        log.error(f"rIC3 failure for query '{btor_path.stem}' (exit {proc.returncode})", FILE_NAME)
        print("crash")
        btor_witness_path.touch()
        return 1

    return 0


def model_check(
    input_path: pathlib.Path, 
    output_path: pathlib.Path, 
    workdir: pathlib.Path,
    model_checker: str, 
    sortcheck: Optional[str],
    catbtor: Optional[str],
    copyback: bool,
    witness: bool,
    int_width: int,
    timeout: int,
    kmax: int,
    engine: str,
    backend_args: list[str],
    cpp: bool,
    debug: int,
    overwrite: bool,
) -> int:
    # TODO: btorsim may be useful for getting full witnesses -- as is it actually
    # does not output valid witness output (header is missing), so we don't use it.
    # NOTE: for a model checker like avr/pono, this might be necessary for full traces
    if not input_path.is_file():
        log.error(f"Source is not a file ({input_path})", FILE_NAME)
        return 1

    if (copyback or witness) and output_path.exists():
        if not overwrite:
            log.error(f"Output path '{output_path}' already exists.", FILE_NAME)
            return 1
    
        if output_path.is_file():
            output_path.unlink()
        elif output_path.is_dir():
            shutil.rmtree(output_path)
    
    src_path = workdir / input_path.name
    btor2_output_path = workdir / "btor2" 
    moxi_path = workdir / input_path.with_suffix(".out.moxi").name
    moxi_witness_path = workdir / input_path.with_suffix(".moxi.witness").name
    moxi_witness_pickle_path = workdir / input_path.with_suffix(".moxi.witness.pickle").name
    nuxmv_witness_path = workdir / input_path.with_suffix(".smv.witness").name

    if input_path.suffix == ".smv":
        witness_path = nuxmv_witness_path
    else:
        witness_path = moxi_witness_path

    shutil.copy(str(input_path), str(src_path))

    start_total = time.perf_counter()

    command = [
        "python3", str(translate_path), str(src_path), "btor2", 
        "--output", str(btor2_output_path),
        "--validate", "--intwidth", str(int_width),
        "--pickle"
    ]
    if sortcheck:
        command.append("--sortcheck")
        command.append(sortcheck)
    if catbtor:
        command.append("--catbtor")
        command.append(catbtor)
    if copyback:
        command.append("--keep")
        command.append(str(moxi_path))
    if cpp:
        command.append("--cpp")
    if debug:
        command.append("--debug")
        command.append(str(debug))

    log.debug(1, f"Translating {input_path}", FILE_NAME)
    log.debug(2, " ".join(command), FILE_NAME)

    try:
        proc = subprocess.run(command, capture_output=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        print("timeout")
        return 1

    end_translate = time.perf_counter()
    time_elapsed = end_translate - start_total

    if debug:
        sys.stderr.write(proc.stderr.decode())

    if proc.returncode:
        if not debug:
            sys.stderr.write(proc.stderr.decode("utf-8"))
        log.error(f"Translation failure for {input_path}", FILE_NAME)
        return proc.returncode
    
    for check_system_path in btor2_output_path.iterdir():
        for btor_path in check_system_path.glob("*.btor2"):
            if model_checker == "btormc":
                retcode = run_btormc(btormc_path, btor_path, int(timeout - time_elapsed), kmax, engine, backend_args)
                if retcode:
                    return retcode
            elif model_checker == "avr":
                retcode = run_avr(avr_path, btor_path, int(timeout - time_elapsed), kmax, engine, backend_args)
                if retcode:
                    return retcode
            elif model_checker == "pono":
                retcode = run_pono(pono_path, btor_path, int(timeout - time_elapsed), kmax, engine, backend_args)
                if retcode:
                    return retcode
            elif model_checker == "ric3":
                retcode = run_ric3(ric3_path, btor_path, int(timeout - time_elapsed), kmax, engine, backend_args)
                if retcode:
                    return retcode
            else:
                log.error(f"Unsupported model checker {model_checker}", FILE_NAME)
                return 1

    retcode = btorwit2moxiwit.main(
        btor2_output_path, moxi_witness_path, 
        verbose=True, do_pickle=(input_path.suffix == ".smv"),
    )

    if retcode:
        return retcode

    if input_path.suffix == ".smv":
        retcode = moxiwit2nuxmvwit.main(
            moxi_witness_pickle_path, nuxmv_witness_path,
        )

        if retcode: 
            return retcode
        
    end_total = time.perf_counter()

    log.debug(1, f"End-to-end done in {end_total-start_total}s", FILE_NAME)

    if copyback:
        shutil.copytree(workdir, output_path)
        log.debug(1, f"Wrote files to {output_path}", FILE_NAME)
    elif witness:
        shutil.copy(witness_path, output_path)
        log.debug(1, f"Wrote witness to {output_path}", FILE_NAME)

    return 0


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("input", 
        help="input program to model check via translation to btor2")
    parser.add_argument("modelchecker", choices=["btormc", "avr", "pono", "ric3"], 
        help="model checker to use")
    parser.add_argument("--output",  
        help="location of output check-system response")
    parser.add_argument("--no-witness", action="store_true",
        help="disable writing of witness file")
    parser.add_argument("--avr-path",
        help="path to avr directory")
    parser.add_argument("--btormc-path",  
        help="path to btormc binary")
    parser.add_argument("--pono-path",
        help="path to pono binary")
    parser.add_argument("--ric3-path",
        help="path to rIC3 binary")
    parser.add_argument("--translate-path",  
        help="path to translate.py script")
    parser.add_argument("--copyback",  action="store_true",
        help="copy all intermediate translations and results to output location")
    parser.add_argument("--intwidth", default=32, type=int, 
        help="bit width to translate Int types to (default=32)")
    parser.add_argument("--catbtor", help="path to catbtor for BTOR2 validation")
    parser.add_argument("--sortcheck", help="path to sortcheck.py for MoXI validation")
    parser.add_argument("--kmax", default=1000, type=int, 
        help="max bound for BMC (default=1000)")
    parser.add_argument("--timeout", default=3600, type=int, 
        help="timeout in seconds for model checker (default=3600)")
    parser.add_argument("--engine", choices=["bmc", "kind", "ic3", "ic3ia", "ic3sa"],
        help="model checking engine (default: bmc); the engines each model checker supports are listed in ENGINE_FLAGS")
    parser.add_argument("--kind", action="store_true", 
        help="alias for '--engine kind'")
    parser.add_argument("--backend-args", default="",
        help="extra arguments appended verbatim to the model checker command (e.g. Pono's solver choice)")
    parser.add_argument("--cpp", action="store_true", 
        help="runs cpp on input if SMV")
    parser.add_argument("--quiet", action="store_true", 
        help="silence output")
    parser.add_argument(
        "--debug",
        nargs="?",
        default=0,
        const=1,
        type=int,
        help="set debug level (0=none, 1=basic, 2=extra)",
    )
    parser.add_argument("--overwrite", action="store_true", 
        help="enable overwriting of output location")
    args = parser.parse_args()

    log.set_debug_level(args.debug)

    if args.quiet:
        log.set_quiet()

    if args.avr_path:
        avr_path = pathlib.Path(args.avr_path)

    if args.btormc_path:
        btormc_path = pathlib.Path(args.btormc_path)

    if args.pono_path:
        pono_path = pathlib.Path(args.pono_path)

    if args.ric3_path:
        ric3_path = pathlib.Path(args.ric3_path)

    engine = args.engine
    if args.kind:
        if engine not in (None, "kind"):
            parser.error(f"--kind conflicts with --engine {engine}")
        engine = "kind"
    if engine is None:
        engine = "bmc"
    if engine not in ENGINE_FLAGS[args.modelchecker]:
        parser.error(f"{args.modelchecker} does not support engine '{engine}' (supported: {', '.join(ENGINE_FLAGS[args.modelchecker])})")

    if args.translate_path:
        translate_path = pathlib.Path(args.translate_path)

    input_path = pathlib.Path(args.input)

    output_path = input_path.with_suffix(".witness").absolute()
    if args.output:
        output_path = pathlib.Path(args.output).absolute()
        
    with tempfile.TemporaryDirectory() as workdir_name:
        workdir = pathlib.Path(workdir_name)
        retcode = model_check(
            input_path=input_path, 
            output_path=output_path, 
            workdir=workdir,
            model_checker=args.modelchecker, 
            sortcheck=args.sortcheck,
            catbtor=args.catbtor,
            copyback=args.copyback, 
            witness=not args.no_witness, 
            int_width=args.intwidth, 
            timeout=args.timeout,
            kmax=args.kmax,
            engine=engine,
            backend_args=shlex.split(args.backend_args),
            cpp=args.cpp,
            debug=args.debug,
            overwrite=args.overwrite
        )

    sys.exit(retcode)
