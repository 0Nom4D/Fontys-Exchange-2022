import 'package:flutter/cupertino.dart';

import 'package:flutter_gen/gen_l10n/app_localizations.dart';

bool isRightToLeftLanguage(BuildContext context) {
  const ltrLocales = ['ar', 'fa', 'he', 'pa', 'ps', 'ur'];
  Locale currentLocale = Localizations.localeOf(context);

  if (ltrLocales.contains(currentLocale.languageCode)) {
    return true;
  }
  return false;
}

bool isPortuguese(BuildContext context) {
  Locale currentLocale = Localizations.localeOf(context);

  return currentLocale.languageCode == "pt";
}

String getLocalizedString(String key, BuildContext context) {
  switch (key) {
    case "las-cumbres":
      return AppLocalizations.of(context)!.las_cumbres;
    case "terminal-list":
      return AppLocalizations.of(context)!.terminal_list;
    case "maisel":
      return AppLocalizations.of(context)!.maisel;
    case "tlou":
      return AppLocalizations.of(context)!.tlou;
    case "motherland":
      return AppLocalizations.of(context)!.motherland;
    case "star-trek-ld":
      return AppLocalizations.of(context)!.star_trek_ld;
    case "vox-machina":
      return AppLocalizations.of(context)!.vox_machina;
    case "the-boys":
      return AppLocalizations.of(context)!.the_boys;
    case "invincible":
      return AppLocalizations.of(context)!.invincible;
    case "cruel-summer":
      return AppLocalizations.of(context)!.cruel_summer;
    case "las-cumbres-desc":
      return AppLocalizations.of(context)!.las_cumbres_desc;
    case "terminal-list-desc":
      return AppLocalizations.of(context)!.terminal_list_desc;
    case "maisel-desc":
      return AppLocalizations.of(context)!.maisel_desc;
    case "tlou-desc":
      return AppLocalizations.of(context)!.tlou_desc;
    case "motherland-desc":
      return AppLocalizations.of(context)!.motherland_desc;
    case "star-trek-ld-desc":
      return AppLocalizations.of(context)!.star_trek_ld_desc;
    case "vox-machina-desc":
      return AppLocalizations.of(context)!.vox_machina_desc;
    case "the-boys-desc":
      return AppLocalizations.of(context)!.the_boys_desc;
    case "invincible-desc":
      return AppLocalizations.of(context)!.invincible_desc;
    case "cruel-summer-desc":
      return AppLocalizations.of(context)!.cruel_summer_desc;
    default:
      break;
  }
  return key;
}