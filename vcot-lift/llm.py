from openai import OpenAI
import tiktoken
from google import genai
import anthropic
import os


def num_tokens_from_string(string):
    encoding = tiktoken.get_encoding("cl100k_base")
    num_tokens = len(encoding.encode(string))
    return num_tokens


# A model is written as "<provider>:<model id>", where <model id> is the name
# the provider's API uses, e.g. "openai:gpt-5.2-2025-12-11". Any model offered
# by a supported provider works, including newly released ones.
#
# The models evaluated in the paper also have the shortcut names below.
MODEL_ALIASES = {
    # OpenAI
    "model_gpt_5_2": "openai:gpt-5.2-2025-12-11",
    "model_gpt_5": "openai:gpt-5-2025-08-07",
    "model_gpt_5_mini": "openai:gpt-5-mini-2025-08-07",
    "model_gpt_4o_mini": "openai:o4-mini-2025-04-16",
    "model_gpt_4_1": "openai:gpt-4.1-2025-04-14",
    "model_gpt_o3": "openai:o3-2025-04-16",
    # Google Gemini
    "gemini_3": "gemini:gemini-3-pro-preview",
    "gemini_3_flash": "gemini:gemini-3-flash-preview",
    "gemini-2.5-pro": "gemini:gemini-2.5-pro",
    "gemini-2.5-flash": "gemini:gemini-2.5-flash",
    # Anthropic
    "claude_sonnet_4_5": "anthropic:claude-sonnet-4-5-20250929",
    "claude_sonnet_4": "anthropic:claude-sonnet-4-20250514",
    "claude_opus_4_1": "anthropic:claude-opus-4-1-20250805",
    "claude_haiku_4_5": "anthropic:claude-haiku-4-5-20251001",
    # DeepSeek
    "deepseek_v3_2": "deepseek:deepseek-chat",
    "deepseek_r1": "deepseek:deepseek-reasoner",
}


class LLM:

    @staticmethod
    def providers():
        """Provider name, as used in "<provider>:<model id>" -> client class."""
        return {
            "openai": LLM.gpt,
            "anthropic": LLM.claude,
            "gemini": LLM.gemini,
            "deepseek": LLM.deepseek,
        }

    @staticmethod
    def parse(spec):
        """Turn a model spec (shortcut name or "<provider>:<model id>") into (provider, model id)."""
        if not isinstance(spec, str):
            raise ValueError(f"Invalid model {spec!r}: expected a string")
        provider, sep, model = MODEL_ALIASES.get(spec, spec).partition(":")
        provider, model = provider.strip().lower(), model.strip()
        if not sep or not provider or not model:
            raise ValueError(
                f'Invalid model "{spec}": use "<provider>:<model id>" '
                f"(providers: {', '.join(LLM.providers())}) "
                f"or a shortcut name from MODEL_ALIASES in llm.py"
            )
        if provider not in LLM.providers():
            raise ValueError(
                f'Unknown provider "{provider}" in model "{spec}". '
                f"Supported providers: {', '.join(LLM.providers())}"
            )
        return provider, model

    @staticmethod
    def create(spec, logger):
        provider, model = LLM.parse(spec)
        return LLM.providers()[provider](model, logger)


    class gpt:
        def __init__(self, model, logger):
            self.client = OpenAI()
            self.model = model
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
        def __init__(self, model, logger):
            self.client = genai.Client()
            self.model = model
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
        def __init__(self, model, logger):
            self.client = anthropic.Anthropic()
            self.model = model
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
        BASE_URL = "https://api.deepseek.com"

        def __init__(self, model, logger):
            self.model = model
            self.logger = logger
            self.client = OpenAI(api_key=os.environ.get('DEEPSEEK_API_KEY'),
                                 base_url=self.BASE_URL)


        def make_query(self, prompt, temperature=1):
            self.logger.info(f"start LLM process, model: {self.model}")
            self.logger.info(f"Token counts: {len(prompt) * 0.3}")

            response = self.client.chat.completions.create(
                model=self.model,
                messages=[
                    {"role": "user", "content": prompt},
                ],
                stream=False
            )

            self.logger.info(f"finish LLM process, model: {self.model}")
            return response.choices[0].message.content
