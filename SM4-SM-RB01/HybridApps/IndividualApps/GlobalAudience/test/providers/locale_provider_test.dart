import 'package:flutter_test/flutter_test.dart';

import 'package:global_audience/src/providers/locale_provider.dart';

void main() {
  test('LocaleProvider creation test', () {
    LocaleProvider prov = LocaleProvider();
    expect(prov.appLocale.languageCode, 'en');
    expect(prov.possibleLocales.length, 9);
  });

  test('LocaleProvider locale update test', () {
    LocaleProvider prov = LocaleProvider();
    expect(prov.appLocale.languageCode, 'en');

    prov.updateLocale('fr');
    expect(prov.appLocale.languageCode, 'fr');
  });

  test('LocaleProvider non available locale update test', () {
    LocaleProvider prov = LocaleProvider();
    expect(prov.appLocale.languageCode, 'en');

    prov.updateLocale('zh');
    expect(prov.appLocale.languageCode, 'en');
  });
}
