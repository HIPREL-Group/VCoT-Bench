import os
from pathlib import Path
from util import grab_verus_code


class Pruner:
    def __init__(self, verus_vs_path, max_iter, model, logger):
        self.verus_vs_path = verus_vs_path
        self.max_iter = max_iter
        self.model = model
        self.logger = logger


    def execute(self, result_path):
        template = Path("./prompts/proof_prune.md").read_text()

        def prune_one_time(verus_path, result_path, i):
            verus_vs = Path(verus_path).read_text()
            qry = template.replace("{{verus_vs}}", verus_vs)

            query_history_path = Path(result_path) / f"proof_prune{i}.md"
            query_history_path.parent.mkdir(parents=True, exist_ok=True)
            query_history_path.write_text(qry)

            response = self.model.make_query(qry)

            response_history_path = Path(result_path) / f"proof_prune_response{i}.md"
            response_history_path.parent.mkdir(parents=True, exist_ok=True)
            response_history_path.write_text(response)

            if "No trivial or redundant proofs" in response:
                self.logger.info("No trivial or redundant proofs found")
                return True
            else:
                verus_pruned = grab_verus_code(response)
                if not verus_pruned:
                    self.logger.error("Response format error! No Verus code or multiple Verus codes found!")
                    raise RuntimeError("response format error!")
                Path(verus_path).write_text(verus_pruned)
                return False

        result_prune_path = os.path.join(result_path, "proof_prune")
        for i in range(self.max_iter):
            self.logger.info(f"start proof pruning {i}")
            ret = prune_one_time(self.verus_vs_path, result_prune_path, i)
            if ret:
                break 