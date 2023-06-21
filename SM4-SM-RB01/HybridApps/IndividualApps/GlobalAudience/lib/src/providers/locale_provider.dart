import 'package:flutter/material.dart';

class LocaleProvider extends ChangeNotifier {
  List<String> possibleLocales = ['ar', 'da', 'de', 'en', 'es', 'fr', 'it', 'nl', 'pt'];
  Locale appLocale = const Locale('en');

  updateLocale(String localeCode) {
    if (possibleLocales.contains(localeCode)) {
      appLocale = Locale(localeCode);
    } else {
      appLocale = const Locale('en');
    }
    notifyListeners();
  }
}