import 'package:flutter/cupertino.dart';

class CountryData {
  CountryData({
    required this.locale,
    required this.flag
  });

  final String locale;
  final AssetImage flag;

  static CountryData arabic = CountryData(locale: 'ar', flag: const AssetImage("assets/countries/arabic.gif"));
  static CountryData danish = CountryData(locale: 'da', flag: const AssetImage("assets/countries/danish.gif"));
  static CountryData german = CountryData(locale: 'de', flag: const AssetImage("assets/countries/german.gif"));
  static CountryData english = CountryData(locale: 'en', flag: const AssetImage("assets/countries/english.gif"));
  static CountryData spanish = CountryData(locale: 'es', flag: const AssetImage("assets/countries/spanish.gif"));
  static CountryData french = CountryData(locale: 'fr', flag: const AssetImage("assets/countries/french.gif"));
  static CountryData portuguese = CountryData(locale: 'pt', flag: const AssetImage("assets/countries/portuguese.gif"));
  static CountryData italian = CountryData(locale: 'it', flag: const AssetImage("assets/countries/italian.gif"));
  static CountryData dutch = CountryData(locale: 'nl', flag: const AssetImage("assets/countries/dutch.gif"));

  static List<CountryData> languages = [
    arabic, danish, german, english, spanish, french, italian, dutch, portuguese
  ];

  static CountryData getFromCode(String localeCode) {
    List<CountryData> possibles = [
      arabic, danish, german, english, spanish, french, italian, dutch, portuguese
    ];

    return possibles.firstWhere((element) => element.locale == localeCode, orElse: () => english);
  }
}