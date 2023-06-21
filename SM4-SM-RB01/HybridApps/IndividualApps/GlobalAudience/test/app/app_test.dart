import 'package:flutter_test/flutter_test.dart';
import 'package:gif_view/gif_view.dart';
import 'package:provider/provider.dart';
import 'package:flutter/material.dart';

import 'package:global_audience/src/providers/locale_provider.dart';
import 'package:global_audience/main.dart';

void main() {
  testWidgets('App creation test', (WidgetTester tester) async {
    LocaleProvider prov = LocaleProvider();

    await tester.pumpWidget(
      MultiProvider(
        providers: [ChangeNotifierProvider(create: (_) => prov)],
        child: const MyApp(),
      )
    );
    expect(find.text("Arthur's Series"), findsOneWidget);
  });

  testWidgets('App language change test', (WidgetTester tester) async {
    LocaleProvider prov = LocaleProvider();

    await tester.pumpWidget(
        MultiProvider(
          providers: [ChangeNotifierProvider(create: (_) => prov)],
          child: const MyApp(),
        )
    );
    expect(find.text("Arthur's Series"), findsOneWidget);

    final popupIcon = find.byIcon(Icons.language);
    expect(popupIcon, findsOneWidget);

    await tester.tap(popupIcon);
    await tester.pumpAndSettle();

    final flagButton = find.byType(PopupMenuItem<String>);
    expect(flagButton, findsNWidgets(9));

    await tester.tap(flagButton.at(5));
    await tester.pumpAndSettle();

    expect(find.text("Les Séries d'Arthur"), findsOneWidget);
  });

  testWidgets('App change language to portuguese', (WidgetTester tester) async {
    LocaleProvider prov = LocaleProvider();

    await tester.pumpWidget(
        MultiProvider(
          providers: [ChangeNotifierProvider(create: (_) => prov)],
          child: const MyApp(),
        )
    );
    expect(find.text("Arthur's Series"), findsOneWidget);

    final popupIcon = find.byIcon(Icons.language);
    expect(popupIcon, findsOneWidget);

    await tester.tap(popupIcon);
    await tester.pumpAndSettle();

    final flagButton = find.byType(PopupMenuItem<String>);
    expect(flagButton, findsNWidgets(9));

    await tester.tap(flagButton.at(8));
    await tester.pumpAndSettle();

    expect(find.byType(GifView), findsAtLeastNWidgets(1));
  });

  testWidgets('App gridview slide test', (WidgetTester tester) async {
    LocaleProvider prov = LocaleProvider();

    await tester.pumpWidget(
        MultiProvider(
          providers: [ChangeNotifierProvider(create: (_) => prov)],
          child: const MyApp(),
        )
    );
    expect(find.text("Arthur's Series"), findsOneWidget);

    final gridView = find.byType(GridView);
    expect(gridView, findsOneWidget);

    await tester.drag(gridView, const Offset(-500, 0));
    await tester.pumpAndSettle();

    final motherlandTitle = find.text("Motherland: Fort Salem");
    expect(motherlandTitle, findsOneWidget);
  });
}
