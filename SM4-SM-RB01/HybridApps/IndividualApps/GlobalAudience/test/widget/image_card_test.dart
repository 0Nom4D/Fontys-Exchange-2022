import 'package:flutter_test/flutter_test.dart';
import 'package:flutter/material.dart';

import 'package:global_audience/src/widgets/image_card.dart';

void main() {
  testWidgets('App creation test', (WidgetTester tester) async {
    await tester.pumpWidget(
      const MaterialApp(
        home: Scaffold(
          body: ImageCard(
            name: "Le Chat Potté 2: La Dernière Quête",
            description: "Le meilleur film de l'histoire de l'animation",
            asset: "vox-machina",
            rating: 15,
          )
        )
      )
    );

    expect(find.text("Le Chat Potté 2: La Dernière Quête"), findsOneWidget);
  });
}