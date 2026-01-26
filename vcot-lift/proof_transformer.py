from pathlib import Path
from util import grab_verus_code
from proof_checker import LemmaChecker, MpChecker, QuantChecker, ThLemmaChecker, UResolutionChecker


class Transformer:
    def __init__(self, verus_vs_path, max_iter, model, logger):
        self.verus_vs_path = verus_vs_path
        self.max_iter = max_iter
        self.model = model
        self.logger = logger
        
    
    def proof_check(self, result_path, z3_proof):
        result_proof_check_path = Path(result_path) / f"proof_check"
        
        # Checkers
        lemma_checker = LemmaChecker(model=self.model, 
                                     verus_path=self.verus_vs_path,
                                     max_iter=1, 
                                     result_path=result_proof_check_path, 
                                     logger=self.logger)
        if lemma_checker.check(z3_proof) == False:
            return False

        mp_checker = MpChecker(model=self.model, 
                               verus_path=self.verus_vs_path,
                               max_iter=1, 
                               result_path=result_proof_check_path, 
                               logger=self.logger)
        if mp_checker.check(z3_proof) == False:
            return False

        quant_checker = QuantChecker(model=self.model, 
                                     verus_path=self.verus_vs_path,
                                     max_iter=1, 
                                     result_path=result_proof_check_path, 
                                     logger=self.logger)
        if quant_checker.check(z3_proof) == False:
            return False

        th_lemma_checker = ThLemmaChecker(model=self.model, 
                                          verus_path=self.verus_vs_path,
                                          max_iter=1, 
                                          result_path=result_proof_check_path, 
                                          logger=self.logger)
        if th_lemma_checker.check(z3_proof) == False:
            return False

        u_resolution_checker = UResolutionChecker(model=self.model, 
                                                  verus_path=self.verus_vs_path,
                                                  max_iter=1, 
                                                  result_path=result_proof_check_path, 
                                                  logger=self.logger)
        if u_resolution_checker.check(z3_proof) == False:
            return False

        self.logger.info("All checks passed!")
        return True
    

    def execute(self, result_path: str, z3_proof:str):
        # get proof_trans template
        template = Path("prompts/proof_trans.md").read_text()

        for iter in range(self.max_iter):
            self.logger.info(f"start proof transformation iter {iter}")
            result_proof_trans_path = Path(result_path) / f"trans_iter{iter}"

            # Get Verus program
            verus_code = Path(self.verus_vs_path).read_text()

            # Proof transformation
            content = template.replace("{{z3_proof}}", z3_proof)
            query = content.replace("{{verus_program}}", verus_code)
            
            # Store proof_trans query
            query_history_path = result_proof_trans_path / "proof_trans.md"
            query_history_path.parent.mkdir(parents=True, exist_ok=True)
            query_history_path.write_text(query)
            
            response = self.model.make_query(query) 

            # Store response
            response_history_path = result_proof_trans_path / "proof_trans_response.md"
            response_history_path.write_text(response)

            verus_vs = grab_verus_code(response)
            if not verus_vs:
                self.logger.error("Response format error! No Verus code or multiple Verus codes found!")
                raise RuntimeError("response format error!")

            # Update Verus code
            Path(self.verus_vs_path).write_text(verus_vs)

            if self.proof_check(result_proof_trans_path, z3_proof) == False:
                self.logger.warning("proof check failed, continue...")
            else:
                self.logger.info("proof check succeed!")
                break