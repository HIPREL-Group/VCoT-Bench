import os
from pathlib import Path
from util import verify, grab_verus_code


class Repair:
    def __init__(self, verus_vs_path, max_iter, model, logger):
        self.verus_vs_path = verus_vs_path
        self.max_iter = max_iter
        self.model = model
        self.logger = logger

    def execute(self, result_path):

        def proof_repair_onetime(result_path, verus_path, error_messages, i):
            self.logger.info(f"start proof repair {i}") 
            # Get proof_repair template
            template = Path("prompts/proof_repair.md").read_text()
            # Get incorrect Verus program
            verus_incorrect = Path(verus_path).read_text()
            # proof repair
            query = template.replace("{{verus_incorrect}}", verus_incorrect)
            query = query.replace("{{error_messages}}", error_messages)

            query_history_path = Path(result_path) / f"proof_repair{i}.md"
            query_history_path.parent.mkdir(parents=True, exist_ok=True)
            query_history_path.write_text(query)

            response = self.model.make_query(query)

            response_history_path = Path(result_path) / f"proof_repair_response{i}.md"
            response_history_path.write_text(response)

            verus_repaired = grab_verus_code(response)
            if not verus_repaired:
                self.logger.error("Response format error! No Verus code or multiple Verus codes found!")
                raise RuntimeError("response format error!")
            Path(verus_path).write_text(verus_repaired)
            
        result, error_messages = verify(str(self.verus_vs_path))
        if result:
            return True

        result_path_repair = os.path.join(result_path, "proof_repair")
        for i in range(self.max_iter):
            proof_repair_onetime(result_path_repair, self.verus_vs_path, error_messages, i)
            result, error_messages = verify(str(self.verus_vs_path))
            if result:
                return True

        self.logger.error(f"Fail to repair the proof after {self.max_iter} iterations!")
        return False