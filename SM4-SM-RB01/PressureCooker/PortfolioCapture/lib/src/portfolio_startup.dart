import 'package:flutter/material.dart';
import 'package:intl/intl.dart';
import 'package:portfolio_capture/providers/portfolio_provider.dart';

import 'package:portfolio_capture/src/portfolio_sections_view.dart';
import 'package:provider/provider.dart';

import '../models/portfolio_model.dart';

class PortfolioStartup extends StatefulWidget {
  static String routeName = "/";

  const PortfolioStartup({super.key});

  @override
  State<StatefulWidget> createState() => PortfolioStartupState();
}

class PortfolioStartupState extends State<PortfolioStartup> {
  @override
  void initState() {
    super.initState();
  }

  Widget createPortfolioCreationDialog(String newName) {
    return AlertDialog(
      title: const Text("New Portfolio"),
      content: TextField(
        maxLines: 1,
        onChanged: (value) => {
          newName = value
        },
        decoration: InputDecoration(
          prefixIcon: const Icon(Icons.edit),
          hintText: "New portfolio title",
          border: OutlineInputBorder(
            borderRadius: BorderRadius.circular(10),
          )
        ),
      ),
      actions: <Widget>[
        TextButton(
          onPressed: () => Navigator.pop(context, null),
          child: const Text('Cancel'),
        ),
        TextButton(
          onPressed: () {
            Navigator.pop(context, newName);
          },
          child: const Text('OK'),
        ),
      ],
    );
  }

  @override
  Widget build(BuildContext context) {
    PortfolioProvider portfolioProvider = Provider.of<PortfolioProvider>(context);

    return portfolioProvider.userPortfolios.isNotEmpty ? Scaffold(
      appBar: AppBar(title: const Text("ProdigyPort")),
      resizeToAvoidBottomInset: true,
      floatingActionButton: FloatingActionButton(
        heroTag: null,
        tooltip: "Create a new portfolio",
        onPressed: () async {
          String? newPortfolioName = await showDialog<String?>(
            context: context,
            builder: (BuildContext context) {
              String newName = "";

              return createPortfolioCreationDialog(newName);
            });

            if (newPortfolioName == null) {
              return;
            }
            portfolioProvider.addPortfolioInList(
              Portfolio(
                id: (portfolioProvider.userPortfolios.length + 1).toString(),
                name: newPortfolioName,
                author: "Me",
                lastModification: DateFormat("yyyy-MM-dd").parse(DateTime.now().toString()),
                sections: [],
              )
            );
        },
        child: const Icon(Icons.add),
      ),
      body: Consumer<PortfolioProvider>(
        builder: (context, provider, _) =>
          ListView.separated(
            padding: const EdgeInsets.all(10),
            itemBuilder: (BuildContext context, int index) {
              return GestureDetector(
                onTap: () {
                  Navigator.push(
                    context,
                    MaterialPageRoute(
                      builder: (context) => PortfolioSections(index)
                    ),
                  );
                },
                child: Card(
                  elevation: 20,
                  child: Column(
                    children: <Widget>[
                      ListTile(
                        leading: const Icon(Icons.file_copy),
                        title: Text(provider.getPortfolioAtIndex(index).name),
                        subtitle: Text("Last modification: ${DateFormat("yyyy/MM/dd").format(provider.getPortfolioAtIndex(index).lastModification)}"),
                        trailing: IconButton(
                          onPressed: () {
                            provider.removePortfolio(provider.getPortfolioAtIndex(index));
                          },
                          icon: const Icon(Icons.cancel_outlined)
                        ),
                      )
                    ],
                  )
                ),
              );
            },
            separatorBuilder: (BuildContext context, int index) => const Divider(),
            itemCount: provider.userPortfolios.length,
          ),
      )
    ) : Scaffold(
      appBar: AppBar(title: const Text("ProdigyPort")),
      resizeToAvoidBottomInset: true,
      body: Center(
        child:Column(
          crossAxisAlignment: CrossAxisAlignment.center,
          mainAxisAlignment: MainAxisAlignment.center,
          children: [
            const Text("You don't have any portfolio."),
            Padding(
              padding: const EdgeInsets.symmetric(vertical: 20),
              child: ElevatedButton(
                onPressed: () async {
                  String? newPortfolioName = await showDialog<String?>(
                    context: context,
                    builder: (BuildContext context) {
                      String newName = "";

                      return createPortfolioCreationDialog(newName);
                    }
                  );

                  if (newPortfolioName == null) {
                    return;
                  }
                  portfolioProvider.addPortfolioInList(
                    Portfolio(
                      id: portfolioProvider.userPortfolios.length.toString(),
                      name: newPortfolioName,
                      author: "Me",
                      lastModification: DateFormat("yyyy-MM-dd").parse(DateTime.now().toString()),
                      sections: [],
                    )
                  );
                },
                child: const Text("Create a new Portfolio")
              ),
            )
          ],
        )
      ),
    );
  }
}