# OpenAI: model_gpt_5_2, model_gpt_5, model_gpt_5_mini, model_gpt_4o_mini, model_gpt_4_1, model_gpt_o3
# Gemini: gemini_3, gemini_3_flash, gemini-2.5-pro, gemini-2.5-flash
# Claude: claude_sonnet_4_5, claude_sonnet_4, claude_opus_4_1, claude_haiku_4_5
# DeepSeek: deepseek_v3_2, deepseek_r1
from openai import OpenAI
import tiktoken
from google import genai
import anthropic
import os


def num_tokens_from_string(string):
    encoding = tiktoken.get_encoding("cl100k_base")
    num_tokens = len(encoding.encode(string))
    return num_tokens


class LLM:

    @staticmethod
    def create(LLM_name, logger):
        if LLM_name in ["model_gpt_5_2", "model_gpt_5", "model_gpt_5_mini", "model_gpt_4o_mini", "model_gpt_4_1", "model_gpt_o3"]:
            return LLM.gpt(LLM_name, logger)
        elif LLM_name in ["gemini_3", "gemini_3_flash", "gemini-2.5-pro", "gemini-2.5-flash"]:
            return LLM.gemini(LLM_name, logger)
        elif LLM_name in ["claude_sonnet_4_5", "claude_sonnet_4", "claude_opus_4_1","claude_haiku_4_5"]:
            return LLM.claude(LLM_name, logger)
        elif LLM_name in ["deepseek_v3_2", "deepseek_r1"]:
            return LLM.deepseek(LLM_name, logger)
        else:
            raise ValueError(f"Unknown model name: {LLM_name}")


    class gpt:
        def __init__(self, LLM_name, logger):
            self.client = OpenAI()
            self.model_config = {
                "model_gpt_5_2": "gpt-5.2-2025-12-11", 
                "model_gpt_5": "gpt-5-2025-08-07",
                "model_gpt_5_mini": "gpt-5-mini-2025-08-07",
                "model_gpt_4o_mini": "o4-mini-2025-04-16", 
                "model_gpt_4_1": "gpt-4.1-2025-04-14", 
                "model_gpt_o3": "o3-2025-04-16"
            }
            self.model = self.model_config[LLM_name]
            self.logger = logger

        def make_query(self, prompt, temperature=1):
            self.logger.info(f"start LLM process, model: {self.model}") 
            self.logger.info("Token counts: {}".format(
                num_tokens_from_string(prompt)
            ))

            response = self.client.responses.create(
                model=self.model,
                input=prompt, 
                temperature=temperature,
            )
            self.logger.info(f"finish LLM process, model: {self.model}")
            return response.output_text


    class gemini:
        def __init__(self, LLM_name, logger):
            self.client = genai.Client()
            self.model_config = {
                "gemini_3": "gemini-3-pro-preview", 
                "gemini_3_flash": "gemini-3-flash-preview", 
                "gemini-2.5-pro": "gemini-2.5-pro",
                "gemini-2.5-flash": "gemini-2.5-flash"
            }
            self.model = self.model_config[LLM_name]
            self.logger = logger
        
        def make_query(self, prompt, temperature=1):
            self.logger.info(f"start LLM process, model: {self.model}") 
            total_tokens = self.client.models.count_tokens(
                model=self.model,
                contents=prompt
            )
            self.logger.info(f"Token counts: {total_tokens.total_tokens}")

            response = self.client.models.generate_content(
                model=self.model,
                contents=prompt,
            )
            self.logger.info(f"finish LLM process, model: {self.model}")
            return response.text

    
    class claude:
        def __init__(self, LLM_name, logger):
            self.client = anthropic.Anthropic()
            self.model_config = {
                "claude_sonnet_4_5": "claude-sonnet-4-5-20250929", 
                "claude_sonnet_4": "claude-sonnet-4-20250514",
                "claude_opus_4_1": "claude-opus-4-1-20250805", 
                "claude_haiku_4_5": "claude-haiku-4-5-20251001"
            }
            self.model = self.model_config[LLM_name]
            self.logger = logger
        
        def make_query(self, prompt, temperature=1):
            self.logger.info(f"start LLM process, model: {self.model}") 
            response = self.client.messages.count_tokens(
                model=self.model,
                messages=[{
                    "role": "user",
                    "content": prompt
                }],
            )
            total_tokens = response.model_dump_json()
            self.logger.info(f"Token counts: {total_tokens}")

            message = self.client.with_options(timeout=1200).messages.create(
                model=self.model, 
                max_tokens=64000,
                messages=[
                    {
                        "role": "user",
                        "content": prompt
                    }
                ]
            )
            self.logger.info(f"finish LLM process, model: {self.model}")
            return message.content[0].text
        
    
    class deepseek:
        def __init__(self, LLM_name, logger):
            self.model = LLM_name
            self.logger = logger
            self.model_config = {
                "deepseek_v3_2": "https://api.deepseek.com",
                "deepseek_r1": "https://api.deepseek.com"
            }
            self.client = OpenAI(api_key=os.environ.get('DEEPSEEK_API_KEY'), 
                                 base_url=self.model_config[LLM_name])
            
            
        def make_query(self, prompt, temperature=1):
            self.logger.info(f"start LLM process, model: {self.model}") 
            self.logger.info(f"Token counts: {len(prompt) * 0.3}")
            
            if self.model == "deepseek_v3_2":
                response = self.client.chat.completions.create(
                    model="deepseek-chat",
                    messages=[
                        {"role": "user", "content": prompt},
                    ],
                    stream=False
                )
            elif self.model == "deepseek_r1":
                response = self.client.chat.completions.create(
                    model="deepseek-reasoner",
                    messages=[
                        {"role": "user", "content": prompt},
                    ],
                    stream=False
                )

            self.logger.info(f"finish LLM process, model: {self.model}") 
            return response.choices[0].message.content
