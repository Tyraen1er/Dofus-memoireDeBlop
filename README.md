# Dofus-memoireDeBlop

Assistant visuel pour le mini-jeu “Mémoire de Blop” de Dofus.  
L’application capture les tuiles cliquées, conserve une courte séquence de leurs évolutions (2 s à 0,2 s d’intervalle) et affiche la grille dans une fenêtre compacte (35 % de la surface d’écran).

## Installation

1. **Prérequis**
   - Python 3.9 ou plus récent.
   - `pip` installé et fonctionnel.
   - Accès aux bibliothèques natives de l’OS pour les captures d’écran :
     - Windows : API GDI (gérée par `mss`/`pywin32`).
     - macOS : autoriser “Screen Recording” et “Accessibility” pour Python/pynput.
     - Linux : un serveur d’affichage compatible X11 (Wayland nécessite souvent un fallback XWayland).

2. **Dépendances Python**
   ```bash
   pip install -r requirements.txt
   ```

## Utilisation

```bash
python3 memoire_de_blop.py
```

- **Mode configuration** : définissez les quatre coins de la grille via ESPACE, ou utilisez la config par défaut.
- **Mode capture** :
  - Renseignez `n`, `m` et la taille de case si besoin.
  - Cliquez dans le jeu ; le programme associe automatiquement la tuile la plus proche et enregistre 10 images sur 2 s.
  - Les tuiles affichent ensuite en boucle la séquence enregistrée, et le panneau latéral montre une carte des clics.

Raccourcis : `Échap` pour revenir au mode configuration pendant une capture (et quitter si vous êtes déjà en mode config), `Espace` pour définir les coins en mode config, `F1` pour lancer la capture.

## Compatibilité et limites selon l’OS

| Fonctionnalité                              | Windows                                    | macOS                                               | Linux                                               |
|---------------------------------------------|--------------------------------------------|-----------------------------------------------------|-----------------------------------------------------|
| Détection automatique de la fenêtre Dofus   | Oui (via `pywin32`)                        | Non : capture plein écran                           | Non : capture plein écran                           |
| Mise à l’échelle DPI                         | Oui (API Windows)                          | Géré via Tkinter + correction Retina               | Géré via Tkinter                                   |
| Autorisations système                       | Aucune spécifique                          | Screen Recording + Accessibility requises           | Peut nécessiter accès X11 complet                  |
| Global mouse listener (`pynput`)            | Support natif                              | Peut demander l’activation d’“Input Monitoring”     | Fonctionne sous X11 (Wayland : support limité)     |

- Sur macOS/Linux, la fenêtre de jeu ne peut pas être identifiée automatiquement : définissez les coins de la grille pour cadrer la capture.
- Sur écrans Retina, les coordonnées logiques/pixels sont réconciliées automatiquement ; pensez malgré tout à positionner la fenêtre du jeu sur l’écran principal si vous avez plusieurs dalles aux échelles différentes.
- Sous Wayland ou sur certains environnements sécurisés, `mss`/`pynput` peuvent être bloqués ; utilisez X11/XWayland ou accordez les privilèges nécessaires.
- L’animation repose sur la capture d’écran : un framerate très bas ou des permissions insuffisantes donneront des tuiles statiques.

## Dépannage rapide

- **Fenêtre vide ou noire** : vérifier les autorisations de capture d’écran (macOS) ou le serveur d’affichage (Linux).
- **Pas de détection de clic** : `pynput` n’a peut-être pas les droits d’accessibilité.
- **Erreurs `pywin32` manquante** : réinstallez `pip install pywin32` (fonctionne uniquement sous Windows).
