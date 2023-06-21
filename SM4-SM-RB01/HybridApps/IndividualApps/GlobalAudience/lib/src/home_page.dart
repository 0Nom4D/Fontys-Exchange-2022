import 'package:gif_view/gif_view.dart';
import 'package:provider/provider.dart';
import 'package:flutter/material.dart';

import 'package:flutter_gen/gen_l10n/app_localizations.dart';

import 'package:global_audience/src/providers/locale_provider.dart';
import 'package:global_audience/src/models/country_data.dart';
import 'package:global_audience/src/widgets/image_card.dart';
import 'package:global_audience/src/translation_utils.dart';
import 'package:global_audience/src/models/serie_data.dart';

class MainPage extends StatefulWidget {
  const MainPage({super.key});

  @override
  MainPageState createState() => MainPageState();
}

class MainPageState extends State<MainPage> {
  String dropdownValue = 'en';

  @override
  Widget build(BuildContext context) {
    LocaleProvider localeProvider = Provider.of<LocaleProvider>(context);
    Orientation currentOrientation = MediaQuery.of(context).orientation;

    return Scaffold(
      appBar: AppBar(
        elevation: 1,
        title: Text(
          AppLocalizations.of(context)!.title,
          style: const TextStyle(fontSize: 24)
        ),
        foregroundColor: Colors.black87,
        backgroundColor: Theme.of(context).colorScheme.background,
        automaticallyImplyLeading: false,
        actions: <Widget>[
          PopupMenuButton<String>(
            icon: const Icon(Icons.language),
            itemBuilder: (context) {
              return CountryData.languages.map<PopupMenuItem<String>>((CountryData value) {
                return PopupMenuItem<String>(
                  value: value.locale,
                  child: Image(
                    image: value.flag,
                    height: 25,
                    width: 45,
                    fit: BoxFit.cover
                  )
                );
              }).toList();
            },
            onSelected: (String? value) {
              setState(() {
                dropdownValue = value!;
              });
              localeProvider.updateLocale(value!);
            },
          )
        ]
      ),
      body: SingleChildScrollView(
        child: Padding(
          padding: const EdgeInsets.all(10),
          child: Column(
            mainAxisSize: MainAxisSize.max,
            crossAxisAlignment: isRightToLeftLanguage(context)
                ? CrossAxisAlignment.end
                : CrossAxisAlignment.start,
            mainAxisAlignment: MainAxisAlignment.start,
            children: <Widget>[
              Padding(
                padding: const EdgeInsets.symmetric(vertical: 20),
                child: Stack(
                  children: <Widget>[
                    Container(
                      height: 60,
                      decoration: BoxDecoration(
                        shape: BoxShape.rectangle,
                        borderRadius: const BorderRadius.all(Radius.circular(10)),
                        gradient: LinearGradient(
                          begin: Alignment.topLeft,
                          end: Alignment.bottomRight,
                          colors: [
                            Theme.of(context).colorScheme.error,
                            const Color(0xFF801B2D)
                          ],
                          tileMode: TileMode.mirror
                        ),
                      ),
                    ),
                    Container(
                      padding: const EdgeInsets.all(7.5),
                      height: 60,
                      alignment: isRightToLeftLanguage(context)
                          ? Alignment.centerRight
                          : Alignment.centerLeft,
                      child: Text(AppLocalizations.of(context)!.carefulMessage),
                    ),
                  ],
                )
              ),
              Padding(
                padding: const EdgeInsets.symmetric(vertical: 4),
                child: Text(
                  AppLocalizations.of(context)!.primeVideo,
                  style: const TextStyle(fontSize: 24)
                ),
              ),
              SizedBox(
                height: isPortuguese(context)
                    ? currentOrientation == Orientation.landscape
                        ? MediaQuery.of(context).size.width * .30
                        : MediaQuery.of(context).size.height * .32
                    : currentOrientation == Orientation.landscape
                        ? MediaQuery.of(context).size.width * .475
                        : MediaQuery.of(context).size.height * .45,
                child: GridView.count(
                  scrollDirection: Axis.horizontal,
                  crossAxisCount: 1,
                  crossAxisSpacing: 10,
                  mainAxisSpacing: 10,
                  childAspectRatio: isPortuguese(context)
                      ? 1.5
                      : 1.75,
                  children: <Widget>[
                    ImageCard.from(SerieData.lasCumbresData),
                    ImageCard.from(SerieData.terminalListData),
                    ImageCard.from(SerieData.missMaiselData),
                    ImageCard.from(SerieData.theLastOfUsData),
                    ImageCard.from(SerieData.theBoysData),
                    ImageCard.from(SerieData.motherlandData),
                    ImageCard.from(SerieData.cruelSummerData),
                    ImageCard.from(SerieData.voxMachinaData),
                    ImageCard.from(SerieData.invincibleData),
                    ImageCard.from(SerieData.starTrekData)
                  ]
                )
              ),
              if (isPortuguese(context))
                Padding(
                  padding: const EdgeInsets.all(5),
                  child: GifView.asset(
                    'assets/siuuuuuuu.gif',
                    height: currentOrientation == Orientation.landscape
                        ? MediaQuery.of(context).size.width * 0.45
                        : MediaQuery.of(context).size.height * 0.335,
                    width: MediaQuery.of(context).size.width,
                    fit: BoxFit.cover,
                    frameRate: 60,
                  )
                )
            ],
          ),
        ),
      )
    );
  }
}
