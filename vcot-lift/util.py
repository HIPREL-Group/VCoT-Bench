import datetime
import re
import subprocess
import tempfile
import json
from pathlib import Path


verus_path = global_config = json.load(open("./config.json", "r")).get("verus_path")


def id_maker() -> str:
    return "{0:%Y-%m-%d-%H%M%S%f}".format(datetime.datetime.now())


def grab_verus_code(llm_response: str) -> str:
    pattern = r"```rust\n([\s\S]*?)\n```"
    matches = re.findall(pattern, llm_response)
    if len(matches) == 1:
        return matches[0].removeprefix("```rust").removesuffix("```")
    else:
        return None


def verify(file_path: str):
    command = f"{verus_path} --num-threads 15 --output-json {file_path}"
    result = subprocess.run(command, shell=True, capture_output=True, text=True)
    if json.loads(result.stdout)["verification-results"]["success"]:
        return (True, None)
    else:
        return (False, result.stderr)


def code_change_is_safe(
    origin,
    changed,
    verus_path,
    logger,
    target_mode=True,
    util_path="./utils",
    inter=False,
    debug=True,
):

    orig_f = tempfile.NamedTemporaryFile(
        mode="w", delete=False, prefix="llm4v_orig", suffix=".rs"
    )
    orig_f.write(origin)
    orig_f.close()

    changed_f = tempfile.NamedTemporaryFile(
        mode="w", delete=False, prefix="llm4v_changed", suffix=".rs"
    )
    changed_f.write(changed)
    changed_f.close()

    cargopath = util_path + "/lynette/source/Cargo.toml"

    opts = []
    if inter:
        opts = ["--asserts-anno"]
    elif target_mode:
        opts = ["-t"]

    verus_compare_cmd = (
        ["cargo", "run", "--manifest-path", cargopath, "--", "compare"]
        + opts
        + [orig_f.name, changed_f.name]
    )

    m = subprocess.run(verus_compare_cmd, capture_output=True, text=True)
    # os.unlink(orig_f.name)
    # os.unlink(changed_f.name)

    if m.returncode == 0:
        return True
    elif m.returncode == 1:
        err_m = m.stdout.strip()
        if err_m == "Files are different":
            return False
        else:
            logger.error(f"Error in comparing code changes: {err_m}")
            return False
    else:
        err_m = m.stderr.strip()
        if "unwrap()" in err_m:
            logger.error(f"Error in comparing code changes: {err_m}")
            return False

    return None


def gain_proof(file_path: str):

    def convert_formula():
        command1 = f"{verus_path} --num-threads 15 --output-json {file_path}"
        command2 = f"{verus_path} --log smt --num-threads 15 {file_path}"
        result = subprocess.run(command1, shell=True, capture_output=True, text=True)
        if not json.loads(result.stdout)["verification-results"]["success"]:
            return False
        result = subprocess.run(command2, shell=True, capture_output=True, text=True)

        trans_path = ".verus-log/root.smt2"

        with open(trans_path, "r") as fp:
            content = fp.read()
            # remove useless output command
            content = content.replace("(get-info :version)", "")
            content = content.replace("(get-info :all-statistics)", "")
            content = content.replace("(check-sat)", "(check-sat)\n (get-proof)")

        with open(".verus-log/converted.smt2", "w") as fp:
            fp.write("(set-option :produce-proofs true)\n")
            fp.write(content)
        
        return True
    
    def split2proof():
        matches = []
        with open(".verus-log/converted.smt2", "r") as fp:
            content = fp.read()
            matches = re.findall(r"\(push\).*?\(pop\)", content, re.DOTALL)
            positions = [match.end() for match in re.finditer(r"\(pop\)", content)]
            for i in range(len(matches)):
                with open(f".verus-log/z3_formula{i}.smt2", "w") as fout:
                    ori_formula = content[:positions[i]]
                    for j in range(i):
                        ori_formula = ori_formula.replace(matches[j], "")
                    fout.write(ori_formula)
                z3_command = f"./z3 .verus-log/z3_formula{i}.smt2 > .verus-log/z3_proof{i}.smt2" 
                result = subprocess.run(z3_command, capture_output=True, shell=True, text=True)
        return len(matches)

    if not convert_formula():
        return False, 0
    num_proof = split2proof()
    return True, num_proof


def rule_selector(proof_rules, proof_content):
    """Select all relevant proof context for the given proof rules."""
    
    def extract_variables(text):
        """Extract all variables (starting with ?, @, or $) from text"""
        return set(re.findall(r'[?@$][a-zA-Z0-9_!.]+', text))
    
    def extract_let_binding(line):
        """
        Extract variable and its definition from a let-binding line.
        Returns (variable, definition_text) or (None, None) if not a let-binding.
        """
        line = line.strip()
        match = re.search(r'\(let\s+\(\(([?@$][a-zA-Z0-9_!.]+)\s+(.+)\)\)', line)
        if match:
            var = match.group(1)
            defn_start = match.start(2)
            defn_text = line[defn_start:]
            defn_text = re.sub(r'\)+$', '', defn_text).strip()
            return var, defn_text
        return None, None
    
    def find_proof_rule_in_line(line, proof_rule):
        """Check if a line contains the given proof rule."""
        text = line.replace("(", " ").replace(")", " ") 
        return proof_rule in text.split(" ") 

    proof_lines = proof_content.split("\n")
    proof_lines = [line for line in proof_lines if line.strip() != ""]

    res_lines = set()
    for i in range(len(proof_lines)):
        if any(find_proof_rule_in_line(proof_lines[i], proof_rule) for proof_rule in proof_rules):
            res_lines.add(i)
            dependencies = extract_variables(proof_lines[i])
            # extract dependencies from previous proof lines
            for j in range(i - 1, -1, -1):
                var, defn = extract_let_binding(proof_lines[j])
                if var and var in dependencies:
                    res_lines.add(j)
                    new_deps = extract_variables(defn)
                    dependencies.update(new_deps)
    
    proof_context = []
    for j in range(len(proof_lines)):
        if j in res_lines:
            proof_context.append(proof_lines[j])

    return "\n".join(proof_context) 


def rule_selector_test(proof_rules, proof_content):
    """Select all relevant proof context for the given proof rules."""
    
    def extract_variables(text):
        """Extract all variables (starting with ?, @, or $) from text"""
        return set(re.findall(r'[?@$][a-zA-Z0-9_!.]+', text))
    
    def extract_let_binding(line):
        """
        Extract variable and its definition from a let-binding line.
        Returns (variable, definition_text) or (None, None) if not a let-binding.
        """
        line = line.strip()
        match = re.search(r'\(let\s+\(\(([?@$][a-zA-Z0-9_!.]+)\s+(.+)\)\)', line)
        if match:
            var = match.group(1)
            defn_start = match.start(2)
            defn_text = line[defn_start:]
            defn_text = re.sub(r'\)+$', '', defn_text).strip()
            return var, defn_text
        return None, None
    
    def find_proof_rule_in_line(line, proof_rule):
        """Check if a line contains the given proof rule."""
        text = line.replace("(", " ").replace(")", " ") 
        return proof_rule in text.split(" ") 

    proof_lines = proof_content.split("\n")
    proof_lines = [line for line in proof_lines if line.strip() != ""]

    res_list = []
    for i in range(len(proof_lines) - 1, -1, -1):
        if any(find_proof_rule_in_line(proof_lines[i], proof_rule) for proof_rule in proof_rules):
            res_lines = set()
            res_lines.add(i)
            dependencies = extract_variables(proof_lines[i])
            # extract dependencies from previous proof lines
            for j in range(i - 1, -1, -1):
                var, defn = extract_let_binding(proof_lines[j])
                if var and var in dependencies:
                    res_lines.add(j)
                    new_deps = extract_variables(defn)
                    dependencies.update(new_deps)
    
            proof_context = []
            for j in range(len(proof_lines)):
                if j in res_lines:
                    proof_context.append(proof_lines[j])

            res_list.append("\n".join(proof_context))
     
    return res_list


if __name__ == "__main__":
    gain_proof("temp.rs")
    pass
    # path = "benchmarks"
    # ans = 0
    # for root, dirs, files in os.walk(path):
    #     for file in files:
    #         if file.endswith(".rs"):
    #             file_path = os.path.join(root, file)
    #             ret, num = gain_proof(file_path)
    #             for i  in range(num):
    #                 with open(f".verus-log/z3_proof{i}.smt2", "r") as fp:
    #                     content = fp.read()
    #                     ans = max(ans, len(content.split("\n")))
    # print(ans)