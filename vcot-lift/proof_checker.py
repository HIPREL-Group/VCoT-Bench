from util import rule_selector
from pathlib import Path
import os


class LemmaChecker:
    def __init__(self, model, verus_path, max_iter, result_path, logger):
        self.model = model
        self.verus_path = verus_path
        self.verus_code = Path(verus_path).read_text()
        self.max_iter = max_iter 
        self.result_path = os.path.join(result_path, "lemma_checker") 
        self.logger = logger

    def check(self, proof_content):
        template = Path("prompts/proof_check/lemma.md").read_text() 
        for i in range(self.max_iter):
            self.logger.info(f"start iteration {i} of LemmaChecker")
            proof_context = rule_selector(["lemma"], proof_content)
            if len(proof_context) > 0:
                qry = template.replace("{{verus_program}}", self.verus_code)
                qry = qry.replace("{{z3_proof}}", proof_context) 

                query_history_path = Path(self.result_path) / f"query{i}.md"
                query_history_path.parent.mkdir(parents=True, exist_ok=True)
                query_history_path.write_text(qry)

                response = self.model.make_query(qry) 

                # Store response
                response_history_path = Path(self.result_path) / f"response{i}.md"
                response_history_path.write_text(response)
                
                if "The proof is complete" in response:
                    self.logger.info("The proof is complete for LemmaChecker")
                    return True
                elif "The proof is incomplete" in response:
                    self.logger.warning("The proof is incomplete for LemmaChecker")
                    return False


class MpChecker:
    def __init__(self, model, verus_path, max_iter, result_path, logger):
        self.model = model
        self.verus_path = verus_path
        self.verus_code = Path(verus_path).read_text()
        self.max_iter = max_iter 
        self.result_path = os.path.join(result_path, "mp_checker") 
        self.logger = logger

    def check(self, proof_content):
        template = Path("prompts/proof_check/mp.md").read_text() 
        for i in range(self.max_iter):
            self.logger.info(f"start iteration {i} of MpChecker")
            proof_context = rule_selector(["mp", "mp~"], proof_content)
            if len(proof_context) > 0:
                qry = template.replace("{{verus_program}}", self.verus_code)
                qry = qry.replace("{{z3_proof}}", proof_context) 

                query_history_path = Path(self.result_path) / f"query{i}.md"
                query_history_path.parent.mkdir(parents=True, exist_ok=True)
                query_history_path.write_text(qry)

                response = self.model.make_query(qry) 

                # Store response
                response_history_path = Path(self.result_path) / f"response{i}.md"
                response_history_path.write_text(response)
                
                if "The proof is complete" in response:
                    self.logger.info("The proof is complete for MpChecker")
                    return True
                elif "The proof is incomplete" in response:
                    self.logger.warning("The proof is incomplete for MpChecker")
                    return False


class QuantChecker:
    def __init__(self, model, verus_path, max_iter, result_path, logger):
        self.model = model
        self.verus_path = verus_path
        self.verus_code = Path(verus_path).read_text()
        self.max_iter = max_iter 
        self.result_path = os.path.join(result_path, "quant_checker") 
        self.logger = logger

    def check(self, proof_content):
        template = Path("prompts/proof_check/quant.md").read_text() 
        for i in range(self.max_iter):
            self.logger.info(f"start iteration {i} of QuantChecker")
            proof_context = rule_selector(["quant-intro", "quant-inst", "skolemize"], proof_content)
            if len(proof_context) > 0:
                qry = template.replace("{{verus_program}}", self.verus_code)
                qry = qry.replace("{{z3_proof}}", proof_context) 

                query_history_path = Path(self.result_path) / f"query{i}.md"
                query_history_path.parent.mkdir(parents=True, exist_ok=True)
                query_history_path.write_text(qry)

                response = self.model.make_query(qry) 

                # Store response
                response_history_path = Path(self.result_path) / f"response{i}.md"
                response_history_path.write_text(response)
                
                if "The proof is complete" in response:
                    self.logger.info("The proof is complete for QuantChecker")
                    return True
                elif "The proof is incomplete" in response:
                    self.logger.warning("The proof is incomplete for QuantChecker")
                    return False


class ThLemmaChecker:
    def __init__(self, model, verus_path, max_iter, result_path, logger):
        self.model = model
        self.verus_path = verus_path
        self.verus_code = Path(verus_path).read_text()
        self.max_iter = max_iter 
        self.result_path = os.path.join(result_path, "th_lemma_checker") 
        self.logger = logger

    def check(self, proof_content):
        template = Path("prompts/proof_check/th_lemma.md").read_text() 
        for i in range(self.max_iter):
            self.logger.info(f"start iteration {i} of ThLemmaChecker")
            proof_context = rule_selector(["th-lemma"], proof_content)
            if len(proof_context) > 0:
                qry = template.replace("{{verus_program}}", self.verus_code)
                qry = qry.replace("{{z3_proof}}", proof_context) 

                query_history_path = Path(self.result_path) / f"query{i}.md"
                query_history_path.parent.mkdir(parents=True, exist_ok=True)
                query_history_path.write_text(qry)

                response = self.model.make_query(qry) 

                # Store response
                response_history_path = Path(self.result_path) / f"response{i}.md"
                response_history_path.write_text(response)
                
                if "The proof is complete" in response:
                    self.logger.info("The proof is complete for ThLemmaChecker")
                    return True
                elif "The proof is incomplete" in response:
                    self.logger.warning("The proof is incomplete for ThLemmaChecker")
                    return False


class UResolutionChecker:
    def __init__(self, model, verus_path, max_iter, result_path, logger):
        self.model = model
        self.verus_path = verus_path
        self.verus_code = Path(verus_path).read_text()
        self.max_iter = max_iter 
        self.result_path = os.path.join(result_path, "unit_resolution_checker") 
        self.logger = logger

    def check(self, proof_content):
        template = Path("prompts/proof_check/unit_resolution.md").read_text() 
        for i in range(self.max_iter):
            self.logger.info(f"start iteration {i} of UResolutionChecker")
            proof_context = rule_selector(["unit-resolution"], proof_content)
            if len(proof_context) > 0:
                qry = template.replace("{{verus_program}}", self.verus_code)
                qry = qry.replace("{{z3_proof}}", proof_context) 

                query_history_path = Path(self.result_path) / f"query{i}.md"
                query_history_path.parent.mkdir(parents=True, exist_ok=True)
                query_history_path.write_text(qry)

                response = self.model.make_query(qry) 

                # Store response
                response_history_path = Path(self.result_path) / f"response{i}.md"
                response_history_path.write_text(response)
                
                if "The proof is complete" in response:
                    self.logger.info("The proof is complete for UResolutionChecker")
                    return True
                elif "The proof is incomplete" in response:
                    self.logger.warning("The proof is incomplete for UResolutionChecker")
                    return False

