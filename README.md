# Epistemic Relevance Abstraction for Multi-Agent Coordination

**Paper** | [**Pedagogical Notebook**](pedagogical_companion.ipynb) | [![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)](https://colab.research.google.com/github/YOUR_USERNAME/epistemic-relevance-abstraction/blob/main/pedagogical_companion.ipynb)

> *Which differences between other agents' behaviors matter for coordination, and which can we safely ignore?*

This repository accompanies the paper:

> Sandy Tanwisuth (2025). **Epistemic Relevance Abstraction for Multi-Agent Coordination.** arXiv preprint.

## Overview

When coordinating with other agents, many surface-level behavioral differences don't change what you should do. This paper develops a framework to automatically discover which differences matter, learn compressed representations that preserve only those differences, and certify that acting on these compressions is safe.

```
Co-policies → Soft Best Responses → Strategic InfoNCE → SEC Embeddings → ΔSEC Certificate
```

### Key contributions

1. **Soft SECs** — Extend Strategic Equivalence Relations to soft best responses, with exponential convergence guarantees
2. **Strategic InfoNCE** — Contrastive objective whose optimal critic recovers a log density ratio aligned with incentive structure
3. **Generalization bounds** — Rademacher-based bounds for InfoNCE; VC/Natarajan sample complexity for linear-probe SEC classification
4. **ΔSEC certificates** — KL-based value-loss bounds with an entropy-to-KL bridge for practical monitoring
5. **Horizon effects** — Constructions showing finite-horizon equivalence can mask long-run value divergence
6. **Diversity preservation** — Embedding separation guarantees preventing collapse of strategically distinct partners

## Repository structure

```
├── main.tex                      # Paper source (LaTeX, ICML 2025 format)
├── appendix.tex                  # Appendix with full proofs
├── references.bib                # Bibliography
├── pedagogical_companion.ipynb   # Interactive tutorial notebook
└── README.md
```

## Pedagogical companion

The [notebook](pedagogical_companion.ipynb) walks through every major result using:

- Plain-language intuitions before each theorem
- A toy 3-action matrix game you can modify
- Visualizations of strategic divergence, embeddings, and certificates
- Working code for the full pipeline (observe → embed → cluster → certify → act)

No game theory or MARL background assumed.

## Quick start

```bash
# Clone the repo
git clone https://github.com/YOUR_USERNAME/epistemic-relevance-abstraction.git
cd epistemic-relevance-abstraction

# Run the notebook locally
pip install numpy scipy matplotlib jupyter
jupyter notebook pedagogical_companion.ipynb

# Or open in Colab (no install needed)
```

## Citation

```bibtex
@article{tanwisuth2025epistemic,
  title={Epistemic Relevance Abstraction for Multi-Agent Coordination},
  author={Tanwisuth, Sandy},
  year={2025},
  note={arXiv preprint}
}
```

## Acknowledgments

This work was initiated during an internship at the Center for Human-Compatible AI (CHAI), UC Berkeley (2024–2025). Additional support was provided by the MATS Program (cohort 8.0) and a Cooperative AI Foundation Early Career Research Grant (2025).

## License

This work is released for academic and research purposes. See [LICENSE](LICENSE) for details.
