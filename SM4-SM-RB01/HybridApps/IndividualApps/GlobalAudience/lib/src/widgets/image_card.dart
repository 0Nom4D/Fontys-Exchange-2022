import 'package:custom_rating_bar/custom_rating_bar.dart';
import 'package:gif_view/gif_view.dart';
import 'package:flutter/material.dart';

import 'package:global_audience/src/models/serie_data.dart';
import 'package:global_audience/src/translation_utils.dart';

class ImageCard extends StatelessWidget {
  const ImageCard({
    required this.asset,
    required this.name,
    required this.description,
    required this.rating,
    super.key
  });

  ImageCard.from(SerieData model, {super.key})
    : asset = model.imageAsset,
      name = model.name,
      description = model.description,
      rating = model.rating;

  final String asset;
  final String name;
  final String description;
  final double rating;

  @override
  Widget build(BuildContext context) {
    return Card(
      elevation: 2,
      child: IntrinsicWidth(
        child: Column(
          crossAxisAlignment: CrossAxisAlignment.stretch,
          children: <Widget>[
            SizedBox(
              height: isPortuguese(context) ? 150 : 100,
              child: isPortuguese(context) ? GifView.asset('assets/siuuuuuuu.gif', frameRate: 60) : Image.asset(
                "assets/$asset.jpg",
                fit: BoxFit.cover,
              ),
            ),
            Container(
              height: isPortuguese(context) ? 25 : 40,
              padding: const EdgeInsets.symmetric(vertical: 4, horizontal: 2),
              alignment: isRightToLeftLanguage(context) ? Alignment.topRight : Alignment.topLeft,
              child: Text(
                getLocalizedString(name, context),
                style: const TextStyle(fontWeight: FontWeight.bold, fontSize: 14)
              ),
            ),
            Container(
              height: isPortuguese(context) ? 20 : 140,
              padding: const EdgeInsets.all(2),
              alignment: isRightToLeftLanguage(context) ? Alignment.topRight : Alignment.topLeft,
              child: Text(
                  getLocalizedString(description, context),
                  style: const TextStyle(fontSize: 10)
              ),
            ),
            if (!isPortuguese(context)) ...[
              const Divider(),
              Padding(
                padding: const EdgeInsets.all(2),
                child: RatingBar.readOnly(
                  alignment: isRightToLeftLanguage(context) ? Alignment.centerRight : Alignment.centerLeft,
                  isHalfAllowed: true,
                  filledIcon: Icons.star,
                  emptyIcon: Icons.star_border,
                  halfFilledIcon: Icons.star_half,
                  initialRating: rating,
                  maxRating: 5,
                  size: 20
                )
              )
            ]
          ]
        ),
      )
    );
  }
}